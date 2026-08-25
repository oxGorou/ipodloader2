/*
 * Basic ATA driver for the ipodlinux bootloader
 * 
 * Supports:
 *  PIO (Polling)
 *  Multiple block reads
 *  LBA48 reads
 *  Block caching
 * 
 *  See ATA-ATAPI-6 specification for operational details of how to talk to an ATA drive.
 *
 * Authors: James Jacobsson ( slowcoder@mac.com )
 *          Vincent Huisman ( dataghost@dataghost.com ) - 5.5 support (double sector reads) - 2007-01-23
 *          Ryan Crosby     ( ryan.crosby@live.com ) - LBA48 support and significant rewrites, documentation and comments - 2020-08-12 -> 2024-XX-XX
 *
 * 
 * In this code, "blocks" (blks) refers to fixed 512 byte units of data. The calling code requests data in units of block count.
 * Regardless of drive sector size, this code must return the expected number of 512 byte blocks, given the requested block count.
 * Luckily, all drives usually emulate 512 byte "logical" sectors, regardless of their physical sector size.
 * This means we don't have to do any translation of sector sizes internally, and for all intents and purposes, block size is equal to sector size.
 * 
 * However, some drives with > 512 byte physical sector sizes cannot read LBA numbers that aren't aligned to physical sector boundaries.
 * A notable example of this is the 80GB iPod 5.5G HDD, which has 1024kb physical sectors, and will error if you attempt to read odd sector sizes.
 * To overcome this, reads are always aligned and expanded to align and match the length of physical sectors. Any additional data read will be cached,
 * to reduce read amplification.
 * 
 */
#include "bootloader.h"
#include "console.h"
#include "ipodhw.h"
#include "minilibc.h"
#include "ata2.h"
#include "ata2_definitions.h"

unsigned int pio_base_addr1,pio_base_addr2;
unsigned int pio_reg_addrs[14];

/* 
 * 8K of cache divided into 16 x 512 byte blocks.
 * When doing >512 byte reads, the drive will overwrite multiple blocks of cache,
 * and then the cache lookup table will be updated to reflect this.
*/
#define CACHE_NUMBLOCKS 16
static uint8  *cachedata;
static uint32 *cacheaddr;
static uint32 *cachetick;
static uint32  cacheticks;

/* These track the last command sent, so that if an error occurs the details can be printed. */
static uint8 last_command = 0;
static uint32 last_sector = 0;
static uint16 last_sector_count = 0;

/*
 * Drive configuration
 */
static struct {
  /* Drive CHS geometry */
  uint16 chs[3];

  /* Non-zero if LBA48 is supported */
  uint8 lba48;

 /*
 * The log2 of the number of 512 byte logical blocks that fit within a physical
 * on-disk sector of the device.
 */
  uint8 alignment_log2;

  /* Number of sectors per block for READ MULTIPLE, set via the
   * SET MULTIPLE MODE command. 1 = single-sector reads. */
  uint8 multisectors;

  /* Non-zero if READ MULTIPLE / READ MULTIPLE_EXT should be used */
  uint8 use_multiple;

  /* Drive power state (see ATA_DRIVE_* below). Used to know whether
   * the drive needs a wake-up reset before the next read. */
  uint8 state;

  /* The total number of sectors the device has */
  uint64 sectors;
} ATAdev;

/* Drive power state constants */
#define ATA_DRIVE_OFF      0
#define ATA_DRIVE_ON       1
#define ATA_DRIVE_SLEEPING 2

/* Forward declaration of static functions (not exported via header file) */
static inline int spinwait_drive_busy(void);
static int wait_for_bsy(void);
static int wait_for_rdy(void);
static int perform_soft_reset(void);
static int check_ata_error(void);
static void ata_clear_intr(void);
static inline void clear_cache(void);
static inline int create_cache_entry(uint32 sector);
static inline int find_cache_entry(uint32 sector);
static inline inline void *get_cache_entry_buffer(int cacheindex);
static void ata_send_read_command(uint32 lba, uint16 count);
static uint32 ata_transfer_block(void *ptr, uint32 count);
static uint32 ata_receive_read_data(void *dst, uint32 count);
static int ata_readblock2(void *dst, uint32 sector, int useCache);
static int set_multiple_mode(int sectors);
static int ata_test_read_sector(uint32 sector);
static int freeze_lock(uint16 *identify_buf);
static int set_features(uint16 *identify_buf);
static int ata_perform_wakeup(void);


inline static void pio_outbyte(unsigned int addr, unsigned char data) {
  outb( data, pio_reg_addrs[ addr ] );
}

inline static void pio_outword(unsigned int addr, unsigned int data) {
  outl( data, pio_reg_addrs[ addr ] );
}

inline static volatile unsigned char pio_inbyte( unsigned int addr ) {
  return( inl( pio_reg_addrs[ addr ] ) );
}

inline static volatile unsigned short pio_inword( unsigned int addr ) {
  return( inl( pio_reg_addrs[ addr ] ) );
}

inline static volatile unsigned int pio_indword( unsigned int addr ) {
  return( inl( pio_reg_addrs[ addr ] ) );
}

inline static void ata_command(uint8 cmd) {
  last_command = cmd;
  pio_outbyte( REG_COMMAND, cmd );
}

#define DELAY400NS { \
 pio_inbyte(REG_ALTSTATUS); pio_inbyte(REG_ALTSTATUS); \
 pio_inbyte(REG_ALTSTATUS); pio_inbyte(REG_ALTSTATUS); \
 pio_inbyte(REG_ALTSTATUS); pio_inbyte(REG_ALTSTATUS); \
 pio_inbyte(REG_ALTSTATUS); pio_inbyte(REG_ALTSTATUS); \
 pio_inbyte(REG_ALTSTATUS); pio_inbyte(REG_ALTSTATUS); \
 pio_inbyte(REG_ALTSTATUS); pio_inbyte(REG_ALTSTATUS); \
 pio_inbyte(REG_ALTSTATUS); pio_inbyte(REG_ALTSTATUS); \
 pio_inbyte(REG_ALTSTATUS); pio_inbyte(REG_ALTSTATUS); \
}

/*
 * Wait until BSY clears.
 * Uses timer_get_current()/timer_passed() for timeout (~30 seconds).
 * Returns 1 on success (BSY cleared), 0 on timeout.
 */
static int wait_for_bsy(void) {
  unsigned long timeout_start = timer_get_current();
  while(pio_inbyte(REG_ALTSTATUS) & STATUS_BSY) {
    if(timer_passed(timeout_start, 30 * TIMER_SECOND)) {
      return 0; /* timeout */
    }
  }
  return 1;
}

/*
 * Wait until drive is ready (BSY cleared and RDY set).
 * First waits for BSY to clear, then waits for RDY.
 * Returns 1 on success, 0 on timeout.
 */
static int wait_for_rdy(void) {
  if(!wait_for_bsy()) {
    return 0;
  }

  unsigned long timeout_start = timer_get_current();
  while(!(pio_inbyte(REG_ALTSTATUS) & STATUS_DRDY)) {
    if(timer_passed(timeout_start, 10 * TIMER_SECOND)) {
      return 0; /* timeout */
    }
  }
  return 1;
}

/*
 * Perform an ATA software reset (SRST).
 * Follows the ATA spec section 9.2 reset protocol.
 * Returns 0 on success, -1 on timeout.
 */
static int perform_soft_reset(void) {
  int retry_count;

  /* Select device */
  pio_outbyte(REG_DEVICEHEAD, 0xA0 | DEVICE_0);
  DELAY400NS;

  /* Assert SRST */
  pio_outbyte(REG_CONTROL, CONTROL_NIEN | CONTROL_SRST);
  mlc_delay_ms(1); /* >= 5us per spec */

  /* Deassert SRST */
  pio_outbyte(REG_CONTROL, CONTROL_NIEN);
  mlc_delay_ms(2); /* > 2ms per spec */

  /* Wait for ready, with retries. Some drives take a while. */
  retry_count = 8;
  do {
    if(wait_for_rdy()) {
      break;
    }
  } while(--retry_count);

  if(!retry_count) {
    return -1;
  }

  return 0;
}

/*
 * Issue SET MULTIPLE MODE command to the drive.
 * This tells the drive how many sectors to transfer per DRQ assertion
 * when using READ MULTIPLE / WRITE MULTIPLE commands.
 * sectors: the number of sectors per block (0 = 256).
 * Returns 0 on success, -1 on error.
 */
static int set_multiple_mode(int sectors) {
  pio_outbyte(REG_DEVICEHEAD, 0xA0 | LBA_ADDRESSING | DEVICE_0);
  if(!wait_for_rdy()) {
    return -1;
  }
  pio_outbyte(REG_SECT_COUNT, sectors & 0xFF);
  pio_outbyte(REG_LBA0, 0);
  pio_outbyte(REG_LBA1, 0);
  pio_outbyte(REG_LBA2, 0);
  ata_command(COMMAND_SET_MULTIPLE_MODE);
  DELAY400NS;
  if(!wait_for_bsy()) {
    return -1;
  }
  uint8 status = pio_inbyte(REG_STATUS);
  if(status & STATUS_ERR) {
    return -1;
  }
  return 0;
}

/*
 * Test whether the drive can read a single (possibly unaligned) sector.
 * Used to detect 512e emulation (drive handles unaligned reads internally).
 * Does NOT call fatal error handlers - returns the result instead.
 * Returns 0 on success (drive supports 512e), -1 on error.
 */
static int ata_test_read_sector(uint32 sector) {
  int timeout;

  pio_outbyte(REG_DEVICEHEAD, 0xA0 | LBA_ADDRESSING | DEVICE_0);

  if(!wait_for_rdy()) {
    return -1;
  }

  pio_outbyte(REG_FEATURES, 0);
  pio_outbyte(REG_CONTROL, CONTROL_NIEN);
  pio_outbyte(REG_SECT_COUNT, 1);
  pio_outbyte(REG_LBA0, sector & 0xFF);
  pio_outbyte(REG_LBA1, (sector >> 8) & 0xFF);
  pio_outbyte(REG_LBA2, (sector >> 16) & 0xFF);

  ata_command(COMMAND_READ_SECTORS);
  DELAY400NS;

  /* Wait for DRQ with timeout */
  timeout = 10 * TIMER_SECOND;
  unsigned long start = timer_get_current();
  while(!((pio_inbyte(REG_ALTSTATUS)) & STATUS_DRQ)) {
    if(pio_inbyte(REG_ALTSTATUS) & STATUS_ERR) {
      /* Error before DRQ - read status to clear */
      pio_inbyte(REG_STATUS);
      return -1;
    }
    if(timer_passed(start, timeout)) {
      return -1;
    }
  }

  /* Read 256 words (512 bytes) of data and discard them */
  for(int i = 0; i < 256; i++) {
    (void)inw(pio_reg_addrs[REG_DATA]);
  }

  /* Wait for BSY to clear */
  wait_for_bsy();

  /* Check final status */
  uint8 status = pio_inbyte(REG_STATUS);
  if(status & (STATUS_ERR | STATUS_DF)) {
    return -1;
  }

  return 0;
}

/*
 * PIO timing values for each mode, from Rockbox ata-pp5020.c pio80mhz[].
 * Index = PIO mode number (0-4).
 */
static const unsigned long pio_timing_table[] = {
  0xC293, /* Mode 0 - always safe */
  0x43A2, /* Mode 1 */
  0x11A1, /* Mode 2 */
  0x7232, /* Mode 3 */
  0x3131, /* Mode 4 */
};

/*
 * Issue SECURITY FREEZE LOCK command if the device supports it.
 * This prevents the device from entering any security state (e.g., user
 * password lock) which could lock out the host permanently.
 * See: Rockbox firmware/drivers/ata.c freeze_lock()
 * See: ATA-ATAPI-6 section 9.15.
 */
static int freeze_lock(uint16 *identify_buf) {
  /* Word 82 bit 1: Security Mode feature set supported */
  if(identify_buf[82] & 0x02) {
    pio_outbyte(REG_DEVICEHEAD, 0xA0 | DEVICE_0);
    if(!wait_for_rdy()) return -1;

    ata_command(COMMAND_SECURITY_FREEZE_LOCK);
    DELAY400NS;

    if(!wait_for_rdy()) return -1;
    mlc_printf("FREEZE LOCK OK\n");
  }
  return 0;
}

/*
 * Negotiate PIO mode, enable write cache, and enable read look-ahead
 * via SET FEATURES command.
 * See: Rockbox firmware/drivers/ata.c set_features()
 *
 * The highest supported PIO mode is determined from IDENTIFY words
 * 53 and 64. SET FEATURES subcommand 0x03 sets the PIO mode, and
 * the controller timing register is updated to match.
 *
 * Returns 0 on success, -1 on error.
 */
static int set_features(uint16 *identify_buf) {
  ipod_t *ipod = ipod_get_hwinfo();
  int pio_mode = 0; /* safe default */

  /* Determine the highest supported PIO mode from IDENTIFY data.
   * Word 53 bit 1: word 64 is valid.
   * Word 64 bits 2:1: PIO modes supported (bit 1 = mode 3, bit 2 = mode 4).
   */
  if(identify_buf[53] & (1 << 1)) {
    if(identify_buf[64] & (1 << 2))
      pio_mode = 4;
    else if(identify_buf[64] & (1 << 1))
      pio_mode = 3;
    else if(identify_buf[64] & (1 << 0))
      pio_mode = 2;
  }

  /* SET FEATURES: set PIO mode (subcommand 0x03, parameter = 8 + mode).
   * Try the highest mode once. If rejected, fall back to mode 0 (one retry).
   */
  pio_outbyte(REG_DEVICEHEAD, 0xA0 | DEVICE_0);
  if(wait_for_rdy()) {
    pio_outbyte(REG_FEATURES, 0x03);
    pio_outbyte(REG_SECT_COUNT, 8 + pio_mode);
    ata_command(COMMAND_SET_FEATURES);
    DELAY400NS;
    if(!wait_for_bsy() || (pio_inbyte(REG_STATUS) & STATUS_ERR)) {
      /* Rejected - try mode 0 if we weren't already there */
      if(pio_mode != 0) {
        pio_mode = 0;
        pio_outbyte(REG_DEVICEHEAD, 0xA0 | DEVICE_0);
        if(wait_for_rdy()) {
          pio_outbyte(REG_FEATURES, 0x03);
          pio_outbyte(REG_SECT_COUNT, 8);
          ata_command(COMMAND_SET_FEATURES);
          DELAY400NS;
          wait_for_bsy();
        }
      }
    }
  }

  /* Update the PIO timing register to match the negotiated mode */
  if(ipod->hw_ver > 3) {
    /* PP5020 */
    if(pio_mode >= 0 && pio_mode <= 4) {
      outl(pio_timing_table[pio_mode], 0xc3000000);
    }
  } else {
    /* PP5002 - same timing register at different address */
    if(pio_mode >= 0 && pio_mode <= 4) {
      outl(pio_timing_table[pio_mode], 0xc0003000);
    }
  }

  /* Enable volatile write cache (subcommand 0x02) */
  pio_outbyte(REG_DEVICEHEAD, 0xA0 | DEVICE_0);
  if(wait_for_rdy()) {
    pio_outbyte(REG_FEATURES, 0x02);
    pio_outbyte(REG_SECT_COUNT, 0);
    ata_command(COMMAND_SET_FEATURES);
    DELAY400NS;
    wait_for_bsy();
    if(!(pio_inbyte(REG_STATUS) & STATUS_ERR)) {
      mlc_printf("Write cache enabled\n");
    }
  }

  /* Enable read look-ahead (subcommand 0xAA) */
  pio_outbyte(REG_DEVICEHEAD, 0xA0 | DEVICE_0);
  if(wait_for_rdy()) {
    pio_outbyte(REG_FEATURES, 0xAA);
    pio_outbyte(REG_SECT_COUNT, 0);
    ata_command(COMMAND_SET_FEATURES);
    DELAY400NS;
    wait_for_bsy();
    if(!(pio_inbyte(REG_STATUS) & STATUS_ERR)) {
      mlc_printf("Read look-ahead enabled\n");
    }
  }

  return 0;
}

/*
 * Wake the drive from sleep/standby state.
 * A soft reset brings the drive back to a ready state, but it also
 * clears the multi-sector mode setting, so that has to be re-issued.
 * Called automatically on first read after sleep.
 * See: Rockbox firmware/drivers/ata.c ata_perform_wakeup()
 */
static int ata_perform_wakeup(void) {
  mlc_printf("Waking drive...\n");

  if(perform_soft_reset() != 0) {
    mlc_printf("Wake reset failed\n");
    return -1;
  }

  /* A reset clears the multi-sector mode setting */
  if(ATAdev.use_multiple) {
    set_multiple_mode(ATAdev.multisectors);
  }

  ATAdev.state = ATA_DRIVE_ON;
  mlc_printf("Drive awake\n");
  return 0;
}

#ifdef HAVE_ATA_SMART
/*
 * Read and display S.M.A.R.T. health data from the drive.
 * This is informational - it doesn't affect drive operation.
 * See: Rockbox firmware/drivers/ata.c ata_smart()
 */
static void ata_read_smart(uint16 *identify_buf) {
  /* Check if SMART is supported (word 82 bit 0) */
  if(!(identify_buf[82] & 0x01)) {
    return;
  }

  uint16 smart_data[256];

  pio_outbyte(REG_DEVICEHEAD, 0xA0 | DEVICE_0);
  if(!wait_for_rdy()) return;

  pio_outbyte(REG_FEATURES, SMART_READ_DATA);
  pio_outbyte(REG_LBA2, 0x4F);
  pio_outbyte(REG_LBA1, 0xC2);
  pio_outbyte(REG_SECT_COUNT, 1);
  ata_command(COMMAND_SMART);
  DELAY400NS;

  if(!wait_for_bsy()) return;

  uint8 status = pio_inbyte(REG_STATUS);
  if(status & STATUS_ERR) {
    /* SMART command failed - read error to clear */
    pio_inbyte(REG_ERROR);
    return;
  }

  if(!(status & STATUS_DRQ)) return;

  /* Read 256 words of SMART data */
  for(int i = 0; i < 256; i++) {
    smart_data[i] = inw(pio_reg_addrs[REG_DATA]);
  }
  wait_for_bsy();

  /* Display key SMART attributes:
   * Word 361: Temperature (current)
   * Word 362: Reallocated sector count (worst)
   * Word 364: Power-on hours
   * Word 5: Normalized air flow temperature
   */
  mlc_printf("SMART: Temp=%dC", smart_data[194] & 0xFF);

  uint16 reallocated = smart_data[197]; /* Reallocated event count */
  if(reallocated > 0) {
    mlc_printf(" REALLOC=%d", reallocated);
  }
  mlc_printf("\n");
}
#endif

uint32 ata_init(void) {
  ipod_t *ipod;

  ipod = ipod_get_hwinfo();

  pio_base_addr1 = ipod->ide_base;
  pio_base_addr2 = pio_base_addr1 + 0x200;

  /*
   * Set up lookup table of ATA register addresses, for use with the pio_ macros
   * Note: The PP chips have their IO registers 4 byte aligned
   */
  pio_reg_addrs[ REG_DATA       ] = pio_base_addr1 + 0 * 4;
  pio_reg_addrs[ REG_FEATURES   ] = pio_base_addr1 + 1 * 4;
  pio_reg_addrs[ REG_SECT_COUNT ] = pio_base_addr1 + 2 * 4; // REG_SECT_COUNT = REG_SECCOUNT_LOW
  pio_reg_addrs[ REG_SECT       ] = pio_base_addr1 + 3 * 4; // REG_SECT       = REG_LBA0
  pio_reg_addrs[ REG_CYL_LOW    ] = pio_base_addr1 + 4 * 4; // REG_CYL_LOW    = REG_LBA1
  pio_reg_addrs[ REG_CYL_HIGH   ] = pio_base_addr1 + 5 * 4; // REG_CYL_HIGH   = REG_LBA2
  pio_reg_addrs[ REG_DEVICEHEAD ] = pio_base_addr1 + 6 * 4;
  pio_reg_addrs[ REG_COMMAND    ] = pio_base_addr1 + 7 * 4;
  pio_reg_addrs[ REG_CONTROL    ] = pio_base_addr2 + 6 * 4;
  pio_reg_addrs[ REG_DA         ] = pio_base_addr2 + 7 * 4;

  /*
   * Black magic
   */
  if( ipod->hw_ver > 3 ) {
    /* PP502x */
    outl(inl(0xc3000028) | 0x20, 0xc3000028);  // clear intr
    outl(inl(0xc3000028) & ~0x10000000, 0xc3000028); // reset?
    
    /* PIO timing for IDE0_PRI_TIMING0.
     * Rockbox originally used 0x10 here (faster PIO), but that causes
     * corrupt data when used with mSATA adapters and some SD adapters.
     * Use the original firmware timing 0xC293 instead, which is safe
     * for all adapters.
     * See Rockbox firmware/target/arm/pp/ata-pp5020.c pio80mhz[].
     */
    outl(0xC293, 0xc3000000);
    outl(0x80002150, 0xc3000004);
  } else {
    /* PP5002 */
    outl(inl(0xc0003024) | 0x80, 0xc0003024);
    outl(inl(0xc0003024) & ~(1<<2), 0xc0003024);
    
    outl(0x10, 0xc0003000);
    outl(0x80002150, 0xc0003004);
  }

  /* Reset ATA device state */
  ATAdev.lba48 = 0;
  ATAdev.alignment_log2 = 0;
  ATAdev.multisectors = 0;
  ATAdev.use_multiple = 0;
  ATAdev.sectors = 0;
  ATAdev.state = ATA_DRIVE_OFF;

  /* Perform a soft reset to initialize the drive to a known state.
   * This is critical for mSATA/SD adapters and SSDs that may not be
   * in a clean state after power-on. Without this, IDENTIFY and
   * subsequent reads may return garbage.
   * See Rockbox firmware/drivers/ata.c perform_soft_reset().
   */
  if(perform_soft_reset() != 0) {
    mlc_printf("ATA reset timeout, trying direct...\n");
  }

  /* 1st things first, check if there is an ATA controller here
   * We do this by writing values to two GP registers, and expect
   * to be able to read them back
   */
  pio_outbyte( REG_DEVICEHEAD, 0xA0 | DEVICE_0 ); /* Device 0 */
  DELAY400NS;
  pio_outbyte( REG_SECT_COUNT, 0x55 );
  pio_outbyte( REG_SECT      , 0xAA );
  pio_outbyte( REG_SECT_COUNT, 0xAA );
  pio_outbyte( REG_SECT      , 0x55 );
  pio_outbyte( REG_SECT_COUNT, 0x55 );
  pio_outbyte( REG_SECT      , 0xAA );

  if( (pio_inbyte( REG_SECT_COUNT ) != 0x55)
    || (pio_inbyte( REG_SECT ) != 0xAA) )
    {
      return(1);
    }

  /*
   * Okay, we're sure there's an ATA2 controller and device, so
   * lets set up the caching
   */

  // cachedata holds the actual data read from the device, in CACHE_BLOCKSIZE byte blocks.
  cachedata  = (uint8 *)mlc_malloc(CACHE_NUMBLOCKS * BLOCK_SIZE);
  // cacheaddr maps each index of the cachedata array to its sector number
  cacheaddr  = (uint32*)mlc_malloc(CACHE_NUMBLOCKS * sizeof(uint32));
  // cachetick maps each index of the cachedata array to its age, for finding LRU
  cachetick  = (uint32*)mlc_malloc(CACHE_NUMBLOCKS * sizeof(uint32));
  
  /* Initialize cache */
  clear_cache();

  ATAdev.state = ATA_DRIVE_ON;
  return(0);
}

static void ata_clear_intr(void)
{
  if( ipod_get_hwinfo()->hw_ver > 3 ) {
    outl(inl(0xc3000028) | 0x30, 0xc3000028); // this hopefully clears all pending intrs
  } else {
    outl(inl(0xc0003024) | 0x80, 0xc0003024);
  }
}

void ata_exit(void)
{
  ata_clear_intr ();
}

/*
 * Spinwait until the drive is not busy, with a timeout.
 * Returns 0 on success, -1 on timeout.
 * Timeout is ~30 seconds (generous for spin-up, tight enough to not hang forever).
*/
static inline int spinwait_drive_busy(void) {
  uint32 timeout = 0x4000000;
  while( pio_inbyte( REG_ALTSTATUS) & STATUS_BSY ) {
    if(--timeout == 0) return -1;
  }
  return 0;
}

/*
 * Checks for ATA error after a command completes.
 * Returns 0 if no error, or a non-zero error code (STATUS_ERR, STATUS_DF, etc.)
 * Does NOT call fatal error handlers - the caller decides what to do.
*/
static inline int check_ata_error(void) {
  uint8 status = pio_inbyte( REG_STATUS );
  if(status & (STATUS_ERR | STATUS_DF)) {
    return status;
  }
  return 0;
}


/*
 * Stops (spins down) the drive
 */
void ata_standby(int cmd_variation)
{
  uint8 cmd = COMMAND_STANDBY;
  // this is just a wild guess from "tempel" - I have no idea if this is the correct way to spin a disk down
  if (cmd_variation == 1) cmd = 0x94;
  if (cmd_variation == 2) cmd = 0x96;
  if (cmd_variation == 3) cmd = 0xE0;
  if (cmd_variation == 4) cmd = 0xE2;
  ata_command(cmd);
  DELAY400NS;

  /* Wait until drive is not busy */
  spinwait_drive_busy();


  /* Read the status register to clear any pending interrupts */
  pio_inbyte( REG_STATUS );

  /*
   * The linux kernel notes mention that some drives might cause an interrupt when put to standby mode.
   * This interrupt is then to be ignored.
   */
  ata_clear_intr();
  ATAdev.state = ATA_DRIVE_SLEEPING;
}

void ata_sleep() {
  ata_command( COMMAND_SLEEP );
  DELAY400NS; DELAY400NS;
  spinwait_drive_busy();
  DELAY400NS; DELAY400NS;
  /*
   * When the device is ready to enter sleep mode, it will set an interrupt and wait.
   * It will then wait until we clear that interrupt by reading the STATUS register
   * to actually enter sleep mode.
   */
  pio_inbyte( REG_STATUS );

  /* The device should now be asleep, and will not respond until a DEVICE_RESET command is sent. */
  ATAdev.state = ATA_DRIVE_SLEEPING;
}

/*
 * Print fixed size uint16 big-endian ASCII string.
*/
static void print_str_be16(uint16 *buff, size_t length) {
  /* Walk backwards from end of string to trim whitespace */
  while((length > 0) && (buff[--length] == ((' ' << 8) + ' ')));

  /* Print each word as big endian (this is why we can't just reinterpret buff as a uint8*) */
  for(int i = 0; i < length; i++) {
      mlc_printf("%c%c", buff[i] >> 8, buff[i] & 0xFF);
  }
}

/*
 * Compares a standard C string to a uint16 big-endian ASCII string.
 *
 * str1: First string as a standard C string.
 * str1_start: The offset in characters into which str1 should start to be compared.
 * str2: Second string as a uint16 big-endian ASCII string.
 * str2_start: The offset in characters into which str2 should start to be compared.
 * length: The length in characters which to compare str1 and str2.
 */
static int strncmp_be16(char* str1, size_t str1_start, uint16* str2, size_t str2_start, size_t length) {
  int result = 0;

  while(length--) {
    char lc = str1[str1_start];
    char rc = (str2_start & 1)
        ? str2[str2_start / 2] & 0xFF /* Right character of uint16 */
        : str2[str2_start / 2] >> 8   /* Left character of uint16 */
        ;
    
    result = lc - rc;
    if(result != 0 || lc == '\0' || rc == '\0') break;

    ++str1_start;
    ++str2_start;
  }

  return result;
}

/*
 * Does some extended identification of the ATA device
 */
void ata_identify(void) {
  uint16 *buff = (uint16*)mlc_malloc(sizeof(uint16) * 256);

  /* Wait for drive to be ready before sending IDENTIFY */
  if(!wait_for_rdy()) {
    mlc_printf("HDD not ready for identify\n");
    mlc_show_fatal_error();
    return;
  }

  pio_outbyte( REG_DEVICEHEAD, 0xA0 | DEVICE_0 );
  pio_outbyte( REG_FEATURES  , 0 );
  pio_outbyte( REG_CONTROL   , CONTROL_NIEN );
  pio_outbyte( REG_SECT_COUNT, 0 );
  pio_outbyte( REG_SECT      , 0 );
  pio_outbyte( REG_CYL_LOW   , 0 );
  pio_outbyte( REG_CYL_HIGH  , 0 );

  ata_command( COMMAND_IDENTIFY_DEVICE );
  DELAY400NS;

  if(!ata_receive_read_data(buff, 1)) {
    mlc_printf("HDD identify failed\n");
    mlc_show_fatal_error();
    return;
  }

  /*
  * Verify the IDENTIFY DEVICE response integrity
  *
  * The use of this word is optional. If bits 7:0 of this word contain the signature A5h, bits 15:8 contain the data
  * structure checksum. The data structure checksum is the two’s complement of the sum of all bytes in words 0
  * through 254 and the byte consisting of bits 7:0 in word 255. Each byte shall be added with unsigned arithmetic,
  * and overflow shall be ignored.
  * The sum of all 512 bytes is zero when the checksum is correct.
  */

  if((buff[255] & 0x00FF) == 0xA5) {
    uint8 calculated_sum = 0;
    for(int i = 0; i < 256; i++) {
      calculated_sum += buff[i] & 0x00FF;
      calculated_sum += buff[i] >> 8;
    }

    if(calculated_sum != 0) {
      /* Checksum error */
      mlc_printf("HDD identify FAIL (checksum mismatch)\n");
      mlc_printf("Integrity word: %04hhX\n", buff[255]);
      mlc_printf("Sum: %d\n", calculated_sum);
      mlc_show_fatal_error();
      return;
    }
    else {
      mlc_printf("HDD identify OK (checksum pass)\n");
    }
  }
  else {
    mlc_printf("HDD identify OK (no checksum)\n");
  }

  /* Major version number */
  if(buff[80] == 0x0000 || buff[80] == 0xFFFF) {
    /* device does not report version */
  }
  else {
    for(int i = 14; i >= 2; i--) {
      if(buff[80] & (1 << i)) {
        if(i > 3) {
          mlc_printf("ATA/ATAPI-%d\n", i);
        }
        else {
          mlc_printf("ATA-%d\n", i);
        }
        break;
      }
    }
  }

  /*
   * This field contains the model number of the device. The contents of this field is an ASCII character string of forty
   * bytes. The device shall pad the character string with spaces (20h), if necessary, to ensure that the string is the
   * proper length. The combination of Serial number (words 10-19) and Model number (words 27-46) shall be unique
   * for a given manufacturer.
   */
  uint16 *hdd_model = &buff[27];
  mlc_printf("HDD Model: ");
  print_str_be16(hdd_model, 20);
  mlc_printf("\n");

  /*
   * This field contains the serial number of the device. The contents of this field is an ASCII character string of
   * twenty bytes. The device shall pad the character string with spaces (20h), if necessary, to ensure that the
   * string is the proper length. The combination of Serial number (words 10-19) and Model number (words 27-46)
   * shall be unique for a given manufacturer.
   */
  uint16 *hdd_serial = &buff[10];
  mlc_printf("HDD Serial: ");
  print_str_be16(hdd_serial, 10);
  mlc_printf("\n");

  /*
   * This field contains the firmware revision number of the device. The contents of this field is an ASCII character
   * string of eight bytes. The device shall pad the character string with spaces (20h), if necessary, to ensure that
   * the string is the proper length.
   */
  uint16 *hdd_fw_rev = &buff[23];
  mlc_printf("HDD FW Rev: ");
  print_str_be16(hdd_fw_rev, 4);
  mlc_printf("\n");

  /* Get CHS geometry info */
  ATAdev.chs[0] = buff[1];
  ATAdev.chs[1] = buff[3];
  ATAdev.chs[2] = buff[6];

  mlc_printf("CHS: %u/%u/%u\n", ATAdev.chs[0], ATAdev.chs[1], ATAdev.chs[2]);

  /*
   * Word 83 is the command set supported flags.
   * Bit 10 = LBA48 supported
   * 
   * Note form the ATA-ATAPI-6 spec:
   * The contents of words (61:60) and (103:100) shall not be used to determine if 48-bit addressing is
   * supported. IDENTIFY DEVICE bit 10 word 83 indicates support for 48-bit addressing. 
   * */
  ATAdev.lba48 = (buff[83] & (1 << 10)) ? 1 : 0;

  if(ATAdev.lba48) {
    mlc_printf("LBA48, ");
   /*
    * Words 100-103 contain a value that is one greater than the maximum LBA address in used addressable space
    * when the 48-bit Addressing feature set is supported. The maximum value that shall be placed in this field is
    * 0000FFFFFFFFFFFFh. Support of these words is mandatory if the 48-bit Address feature set is supported.
    */
    ATAdev.sectors = (
          ((uint64)buff[103] << 48)
        | ((uint64)buff[102] << 32)
        | ((uint64)buff[101] << 16)
        | ((uint64)buff[100] << 0)
        );
  }
  else {
    mlc_printf("LBA28, ");

   /*
    * Words (61:60) shall contain the value one greater than the largest user-addressable
    * sector in 28-bit addressing and shall not exceed 0FFFFFFFh. The content of words (61:60) shall
    * be greater than or equal to one and less than or equal to 268,435,455.
    */
    ATAdev.sectors = (
        ((uint64)buff[61] << 16)
      | ((uint64)buff[60] << 0)
      );
  }

  uint64 size_mb = ATAdev.sectors/BLOCKS_PER_MB;
  mlc_printf("Size: %lu.%luGB\n", (uint32)(size_mb / 1024), (uint32)((size_mb % 1024) / 10));

  /*
   * Determine physical sector size from IDENTIFY word 106.
   * Word 106 bits 15:13 indicate whether the field is valid:
   *   Bit 15 = 0, Bit 14 = 1, Bit 13 = 1 -> valid.
   * Bits 3:0 give log2 of (physical sector size / logical sector size).
   * If valid, the physical sector multiplier is 1 << (word106 & 0xF).
   *
   * See: ATA-ATAPI-8 specification, Word 106.
   * See: Rockbox firmware/drivers/ata-common.c ata_get_phys_sector_mult()
   */
  uint32 phys_sector_mult = 1;
  if((buff[106] & 0xe000) == 0x6000) {
    /* Word 106 is valid */
    phys_sector_mult = 1u << (buff[106] & 0x000f);
    mlc_printf("Physical sector mult: %lu\n", phys_sector_mult);
  } else {
    /* Word 106 not reported. Fall back to model-based heuristic. */
    if(strncmp_be16("TOSHIBA ", 0, hdd_model, 0, sizeof("TOSHIBA ") - 1) == 0
      && strncmp_be16("10GAH", 0, hdd_model, 12, sizeof("10GAH") - 1) == 0)
    {
      mlc_printf("TOSHIBA 10GAH detected\n");
      phys_sector_mult = 2;
    }
  }

  if(phys_sector_mult > 1) {
    /*
     * The device reports large physical sectors. Check if it actually
     * needs aligned reads by testing a read of sector 1 (which is
     * NOT aligned to a physical sector boundary for mult > 1).
     * If the read succeeds, the device supports 512e emulation and
     * handles alignment internally - we don't need to align.
     *
     * See: Rockbox firmware/drivers/ata-common.c ata_get_phys_sector_mult()
     */
    mlc_printf("Testing 512e emulation...\n");
    if(ata_test_read_sector(1) == 0) {
      mlc_printf("512e OK, using 512-byte reads\n");
      ATAdev.alignment_log2 = 0;
    } else {
      mlc_printf("No 512e, aligning to %lu sectors\n", phys_sector_mult);
      /* Find log2 of phys_sector_mult */
      uint32 mult = phys_sector_mult;
      ATAdev.alignment_log2 = 0;
      while(mult > 1) {
        ATAdev.alignment_log2++;
        mult >>= 1;
      }
    }
  } else {
    /* 512-byte physical sectors */
    ATAdev.alignment_log2 = 0;
  }

  mlc_printf("Alignment: %d (read %d sectors)\n",
    ATAdev.alignment_log2, (1 << ATAdev.alignment_log2));

  /*
   * SET MULTIPLE MODE: let the drive transfer several sectors per DRQ,
   * which speeds up big reads (kernel and Rockbox images).
   *
   * The block size comes from IDENTIFY word 47 bits 7:0 (bit 8 = valid).
   * If that is not valid, fall back to word 59 bits 7:0, which holds the
   * current setting (bit 8 = valid).
   */
  ATAdev.multisectors = 0;
  ATAdev.use_multiple = 0;
  if(buff[47] & 0x100) {
    ATAdev.multisectors = buff[47] & 0xFF;
  }
  if(ATAdev.multisectors == 0 && (buff[59] & 0x100)) {
    ATAdev.multisectors = buff[59] & 0xFF;
  }

  if(ATAdev.multisectors > 1) {
    if(set_multiple_mode(ATAdev.multisectors) == 0) {
      mlc_printf("SET MULTIPLE MODE %d OK\n", ATAdev.multisectors);
      ATAdev.use_multiple = 1;
    } else {
      mlc_printf("SET MULTIPLE MODE failed, using single-sector\n");
      ATAdev.multisectors = 1;
    }
  }

  /* Negotiate PIO mode, enable write cache and read look-ahead.
   * This also updates the controller timing register to match.
   * See: Rockbox firmware/drivers/ata.c set_features()
   */
  set_features(buff);

  /* Issue SECURITY FREEZE LOCK to prevent security state lockout.
   * See: Rockbox firmware/drivers/ata.c freeze_lock()
   */
  freeze_lock(buff);

  /* Read and display S.M.A.R.T. health data (informational).
   * See: Rockbox firmware/drivers/ata.c ata_smart()
   */
#ifdef HAVE_ATA_SMART
  ata_read_smart(buff);
#endif

  #if DEBUG
    mlc_show_critical_error();
  #endif
}

/*
 * lba:       The Logical Block Adddress to begin reading blocks from.
 * count:     The number of logical blocks to read.
*/
static void ata_send_read_command(uint32 lba, uint16 count) {
  last_sector = lba;
  last_sector_count = count;

  /* Select device and wait for it to be ready.
   * See: Rockbox firmware/drivers/ata.c ata_transfer_sectors()
   */
  pio_outbyte( REG_DEVICEHEAD, 0xA0 | DEVICE_0 );
  if(!wait_for_rdy()) return;

  if(ATAdev.lba48) {
    /*
    * LBA48: write high byte first, then low byte, to the SAME register address.
    * The device latches the first write as the high byte and the second as the low byte.
    * See: Rockbox firmware/drivers/ata.c ata_transfer_sectors()
    */

    /* Sector count: high then low, same address */
    pio_outbyte( REG_SECCOUNT_LOW , (count >> 8) & 0xff  );
    pio_outbyte( REG_SECCOUNT_LOW , count & 0xff  );

    /* LBA Low: bits 31:24 (high) then bits 7:0 (low) */
    pio_outbyte( REG_LBA0         , (lba >> 24) & 0xff );
    pio_outbyte( REG_LBA0         , lba & 0xff  );

    /* LBA Mid: bits 39:32 (high, always 0 for uint32) then bits 15:8 (low) */
    pio_outbyte( REG_LBA1         , 0 );
    pio_outbyte( REG_LBA1         , (lba >> 8) & 0xff );

    /* LBA High: bits 47:40 (high, always 0 for uint32) then bits 23:16 (low) */
    pio_outbyte( REG_LBA2         , 0 );
    pio_outbyte( REG_LBA2         , (lba >> 16) & 0xff );

    /* Device/Head: LBA mode, drive 0 - written last, before command */
    pio_outbyte( REG_DEVICEHEAD, 0xA0 | LBA_ADDRESSING | DEVICE_0 );
  }
  else {
    /* LBA28: sector count, LBA low/mid/high, then head in Device/Head */
    pio_outbyte( REG_SECCOUNT_LOW , count & 0xff  );
    pio_outbyte( REG_LBA0         , lba & 0xff  );
    pio_outbyte( REG_LBA1         , (lba >> 8) & 0xff );
    pio_outbyte( REG_LBA2         , (lba >> 16) & 0xff );

    /* Device/Head: LBA bits 27:24 in lower nibble, LBA mode, drive 0 - written last, before command */
    pio_outbyte( REG_DEVICEHEAD, 0xA0 | ((lba >> 24) & 0x0f) | LBA_ADDRESSING | DEVICE_0 );
  }

  /* Send read command - use READ MULTIPLE if configured.
   * With READ MULTIPLE, the drive presents multisectors per DRQ, but
   * the per-sector read loop still works because DRQ stays set during
   * the entire multi-sector block - the host can read words at any pace.
   * This matches Rockbox's approach for faster large transfers.
   */
  if(ATAdev.lba48) {
    if(ATAdev.use_multiple) {
      ata_command( COMMAND_READ_MULTIPLE_EXT );
    } else {
      ata_command( COMMAND_READ_SECTORS_EXT );
    }
  }
  else {
    if(ATAdev.use_multiple) {
      ata_command( COMMAND_READ_MULTIPLE );
    } else {
      ata_command( COMMAND_READ_SECTORS );
    }
  }

  DELAY400NS;  DELAY400NS;
}

/*
 * Copies blocks of data (512 bytes each) from the device
 * to host memory.
 * 
 * *ptr: Destination buffer. If NULL, data will be read from the device and discarded.
 * count: The number of 512 byte blocks to read from the device into the buffer
 * return: The number of bytes actually read from the device
 */
static uint32 ata_transfer_block(void *ptr, uint32 count) {
  // Data is read in as 16 bit words, so 2 bytes at a time.
  uint32 words = (BLOCK_SIZE / 2) * count;
  uint32 words_received = 0;

  if(ptr != NULL) {
    uint16 *dst = (uint16*)ptr;
    while(words--) {
      /* Wait until drive is not busy */
      if(spinwait_drive_busy()) return words_received * 2;

      /* Check DRQ to see if there's more data to read, or if an error has occured */
      if((pio_inbyte(REG_STATUS) & (STATUS_ERR | STATUS_DRQ)) != STATUS_DRQ) {
        break;
      }

      /* Read another 16 bits of data into buffer */
      *dst++ = inw( pio_reg_addrs[REG_DATA] );
      ++words_received;
    }
  }
  else {
    while(words--) {
      /* Wait until drive is not busy */
      if(spinwait_drive_busy()) return words_received * 2;

      /* Check DRQ to see if there's more data to read, or if an error has occured */
      if((pio_inbyte(REG_STATUS) & (STATUS_ERR | STATUS_DRQ)) != STATUS_DRQ) {
        break;
      }

      /* Read another 16 bits of data and discard it */
      inw( pio_reg_addrs[REG_DATA] );
      ++words_received;
    }
  }

  return words_received * 2;
}

/*
 * Receive data back from the device after a read out command has been issued.
 *
 * *dst: Destination buffer. If NULL, data will be read from the device and discarded.
 * count: The number of 512 byte blocks to read from the device into the buffer
 * Returns: number of bytes actually read, or 0 on error.
*/
static uint32 ata_receive_read_data(void *dst, uint32 count) {
  uint32 bytesread;
  bytesread = ata_transfer_block(dst, count);

  /* Wait for any final busy state to clear */
  if(spinwait_drive_busy()) return 0;

  /* Check if reading ended on an error */
  if(check_ata_error()) {
    return 0;
  }

  /* Verify we read the expected number of bytes */
  if(bytesread != count * BLOCK_SIZE) {
    return 0;
  }

  return bytesread;
}

static inline void clear_cache(void) {
  int i;

  cacheticks = 0;

  for(i = 0; i < CACHE_NUMBLOCKS; i++) {
    cachetick[i] =  0;  /* Time is zero */
    cacheaddr[i] = ~0;  /* Invalid sector number */
  }
}

/* 
 * Creates a cache entry for a given sector, and returns the index of the cache buffer
 * that was created.
*/
static inline int create_cache_entry(uint32 sector) {
  int cacheindex;
  int i;

  cacheindex = find_cache_entry(sector);

  if(cacheindex < 0) {
    cacheindex = 0;
    for(i = 0; i < CACHE_NUMBLOCKS; i++) {
      if( cachetick[i] < cachetick[cacheindex] ) {
        cacheindex = i;
      }
    }
  }

  cacheaddr[cacheindex] = sector;
  cachetick[cacheindex] = cacheticks;

  return(cacheindex);
}

static inline int find_cache_entry(uint32 sector) {
  if(sector == ~0) {
    return(-1);
  }

  for(int i = 0; i < CACHE_NUMBLOCKS; i++) {
    if( cacheaddr[i] == sector ) {
      /* cacheticks is incremented every time the cache is hit */
      cachetick[i] = ++cacheticks;
      return(i);
    }
  }

  return(-1);
}

static inline void *get_cache_entry_buffer(int cacheindex) {
    if(cacheindex >= 0 && cacheindex < CACHE_NUMBLOCKS) {
      return(cachedata + (BLOCK_SIZE * cacheindex));
    }
    else {
      mlc_printf(
      "Invalid cache index!\n"
      "Index %d is out of bounds.\n"
      , cacheindex);

      mlc_show_fatal_error();
      return NULL;
    }
}

/*
 * Sets up the transfer of one block of data.
 * Includes retry logic: on error, performs a soft reset and retries.
 * Returns 0 on success, -1 on unrecoverable error.
 */
static int ata_readblock2(void *dst, uint32 sector, int useCache) {
  int retries = 3;

  /* If the drive is sleeping/standby, wake it up first.
   * This performs a full soft reset + re-identify + re-set features.
   */
  if(ATAdev.state == ATA_DRIVE_SLEEPING) {
    if(ata_perform_wakeup() != 0) {
      return -1;
    }
    clear_cache();
  }

  /*
   * Check if we have this block in cache first
   */
  if (useCache) {
    int cacheindex = find_cache_entry(sector);
    if( cacheindex >= 0 ) {
        /* In cache! No need to bother the ATA controller */
      void *cachedsrc = get_cache_entry_buffer(cacheindex);
      mlc_memcpy(dst, cachedsrc, BLOCK_SIZE);
      return(0);
    }
  }

  if(!ATAdev.lba48 && (sector > 0x0FFFFFFF)) {
    /* The sector is too large for the current addressing scheme */
    mlc_printf(
      "Out of bounds read!\n"
      "Sector %lu is too large for LBA28 addressing.\n"
      , sector);
    mlc_show_fatal_error ();
    return(-1);
  }

  /* Calculate an aligned LBA for the specified sector */
  uint16 read_size = (1u << ATAdev.alignment_log2);
  uint32 sector_mask = ~((1u << (ATAdev.alignment_log2)) - 1u);
  uint32 sector_to_read = sector & sector_mask;

retry:
  /* Send the read command to the device*/
  ata_send_read_command(sector_to_read, read_size);

  if (useCache) {
    /*
      * In cached mode, store every 512 byte block we read into the cache,
      * and then copy the requested sector out to dst
    */
    for(uint32 i = sector_to_read; i < (sector_to_read + read_size); i++) {
      int cacheindex = create_cache_entry(i);
      void *cachedst = get_cache_entry_buffer(cacheindex);

      /* Read data directly into the cache*/
      int bytesread = ata_receive_read_data(cachedst, 1);

      if(bytesread == 0) {
        /* Read failed - try soft reset and retry */
        if(--retries > 0) {
          mlc_printf("Read err at sec %lu, retrying... (%d left)\n", sector, retries);
          clear_cache();
          if(perform_soft_reset() == 0) {
            /* A reset clears the multi-sector mode setting */
            if(ATAdev.use_multiple) {
              set_multiple_mode(ATAdev.multisectors);
            }
            goto retry;
          }
        }
        mlc_printf("Read FAILED at sector %lu\n", sector);
        return(-1);
      }

      if(i == sector) {
        /* This is the sector that was actually requested, copy it out of the cache block into the destination */
        mlc_memcpy(dst, cachedst, bytesread);
      }
    }
    cacheticks++;
  }
  else {
    /*
      * In non-cached mode, discard the sectors we read unless
      * they were the requested sector.
    */
    for(uint32 i = sector_to_read; i < (sector_to_read + read_size); i++) {
      uint32 bytesread;
      if(i == sector) {
        /* This is the sector that was actually requested, read data directly into the destination */
        bytesread = ata_receive_read_data(dst, 1);
      }
      else {
        /* Discard data we can't use */
        bytesread = ata_receive_read_data(NULL, 1);
      }

      if(bytesread == 0) {
        if(--retries > 0) {
          mlc_printf("Read err at sec %lu, retrying... (%d left)\n", sector, retries);
          if(perform_soft_reset() == 0) {
            /* A reset clears the multi-sector mode setting */
            if(ATAdev.use_multiple) {
              set_multiple_mode(ATAdev.multisectors);
            }
            goto retry;
          }
        }
        mlc_printf("Read FAILED at sector %lu\n", sector);
        return(-1);
      }
    }
  }

  return(0);
}

int ata_readblock(void *dst, uint32 sector) {
  return ata_readblock2(dst, sector, 1);
}

int ata_readblocks(void *dst, uint32 sector, uint32 count) {
  int err;
  while (count-- > 0) {
    err = ata_readblock2 (dst, sector++, 1);
    if (err) return err;
    dst = (char*)dst + BLOCK_SIZE;
  }
  return 0;
}

int ata_readblocks_uncached (void *dst, uint32 sector, uint32 count) {
  int err;
  while (count-- > 0) {
    err = ata_readblock2 (dst, sector++, 0);
    if (err) return err;
    dst = (char*)dst + 512;
  }
  return 0;
}
