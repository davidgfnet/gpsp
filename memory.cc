/* gameplaySP
 *
 * Copyright (C) 2006 Exophase <exophase@gmail.com>
 * Copyright (C) 2024 David Guillen Fandos <david@davidgf.net>
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 2 of
 * the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
 */

extern "C" {
  #include "common.h"
  #include "streams/file_stream.h"
}
#include "gba_memory_cpp.h"

// Flash devices and manufacturers
#define FLASH_DEVICE_UNDEFINED       0x00
#define FLASH_DEVICE_MACRONIX_64KB   0x1C
#define FLASH_DEVICE_AMTEL_64KB      0x3D
#define FLASH_DEVICE_SST_64K         0xD4
#define FLASH_DEVICE_PANASONIC_64KB  0x1B
#define FLASH_DEVICE_MACRONIX_128KB  0x09

#define FLASH_MANUFACTURER_MACRONIX  0xC2
#define FLASH_MANUFACTURER_AMTEL     0x1F
#define FLASH_MANUFACTURER_PANASONIC 0x32
#define FLASH_MANUFACTURER_SST       0xBF

u8 bios_rom[1024 * 16];

// Up to 128kb, store SRAM, flash ROM, or EEPROM here.
u8 gamepak_backup[1024 * 128];

// ROM memory is allocated in blocks of 1MB to better map the native block
// mapping system. We will try to allocate 32 of them to allow loading
// ROMs up to 32MB, but we might fail on memory constrained systems.

u8 *gamepak_buffers[32];    /* Pointers to malloc'ed blocks */
u32 gamepak_buffer_count;   /* Value between 1 and 32 */
u32 gamepak_size;           /* Size of the ROM in bytes */
// We allocate in 1MB chunks.
const unsigned gamepak_buffer_blocksize = 1024*1024;

// LRU queue with the loaded blocks and what they map to
struct {
  u16 next_lru;             /* Index in the struct to the next LRU entry */
  s16 phy_rom;              /* ROM page number (-1 means not mapped) */
} gamepak_blk_queue[1024];

u16 gamepak_lru_head;
u16 gamepak_lru_tail;

// Stick page bit: prevents page eviction for a frame. This is used to prevent
// unmapping code pages while being used (ie. in the interpreter).
u32 gamepak_sticky_bit[1024/32];

#define gamepak_sb_test(idx) \
 (gamepak_sticky_bit[((unsigned)(idx)) >> 5] & (1 << (((unsigned)(idx)) & 31)))

// This is global so that it can be kept open for large ROMs to swap
// pages from, so there's no slowdown with opening and closing the file
// a lot.
RFILE *gamepak_file_large = NULL;

// Writes to these respective locations should trigger an update
// so the related subsystem may react to it.

u32 backup_type = BACKUP_UNKN;
u32 backup_type_reset = BACKUP_UNKN;
u32 flash_mode = FLASH_BASE_MODE;
u32 flash_command_position = 0;
u32 flash_bank_num;  // 0 or 1
u32 flash_bank_cnt;

u32 flash_device_id = FLASH_DEVICE_MACRONIX_64KB;

// Funny memory areas and their read handlers:

template <typename rdtype> inline rdtype unmapped_rom_read(u32 address);
template <typename rdtype> inline rdtype read_openbus(u32 address);
template <typename rdtype> inline rdtype read_backup(u32 address);

// Unmapped ROM area returns some funny value left in the bus (the address)
template <> inline u8 unmapped_rom_read(u32 addr) {
  return (((addr) >> 1) >> (((addr) & 1) * 8)) & 0xFF;
}
template <> inline u16 unmapped_rom_read(u32 addr) {
  return ((addr) >> 1) & 0xFFFF;
}
template <> inline u32 unmapped_rom_read(u32 addr) {
  return ((((addr) & ~3) >> 1) & 0xFFFF) | (((((addr) & ~3) + 2) >> 1) << 16);
}

// Open BUS reads returns some future opcode (prefetch?)
template <> inline u8 read_openbus(u32 address) {
  if (reg[REG_CPSR] & 0x20)
    return read_memory8(reg[REG_PC] + 4 + (address & 0x01));
  else
    return read_memory8(reg[REG_PC] + 8 + (address & 0x03));
}
template <> inline u16 read_openbus(u32 address) {
  if (reg[REG_CPSR] & 0x20)
    return read_memory16(reg[REG_PC] + 4);
  else
    return read_memory16(reg[REG_PC] + 8 + (address & 0x02));
}
template <> inline u32 read_openbus(u32 address) {
  if (reg[REG_CPSR] & 0x20) {
    u32 instv = read_memory16(reg[REG_PC] + 4);
    return instv | (instv << 16);
  } else
    return read_memory32(reg[REG_PC] + 8);
}

// It just reads at byte level, and replicates byte for larger reads.
template <> inline u8 read_backup(u32 address) {
  return read_backup(address & 0xFFFF);
}
template <> inline u16 read_backup(u32 address) {
  u16 value = read_backup(address & 0xFFFF);
  return value | (value << 8);
}
template <> inline u32 read_backup(u32 address) {
  u32 value = read_backup(address & 0xFFFF);
  return value | (value << 8) | (value << 16) | (value << 24);
}

u8 read_backup(u32 address) {
  u8 value = 0;

  if(backup_type == BACKUP_EEPROM)
    return 0xff;

  if(backup_type == BACKUP_UNKN)
    backup_type = BACKUP_SRAM;

  if (backup_type == BACKUP_SRAM)
    return gamepak_backup[address];
  else if (flash_mode == FLASH_ID_MODE) {
    if (flash_bank_cnt == FLASH_SIZE_128KB) {
      if (address == 0x0000)     /* ID manufacturer type */
        return FLASH_MANUFACTURER_MACRONIX;
      else if(address == 0x0001) /* ID device type */
        return FLASH_DEVICE_MACRONIX_128KB;
    } else {
      if (address == 0x0000)     /* ID manufacturer type */
        return FLASH_MANUFACTURER_PANASONIC;
      else if(address == 0x0001) /* ID device type */
        return FLASH_DEVICE_PANASONIC_64KB;
    }
  } else {
    u32 fulladdr = address + 64*1024*flash_bank_num;
    return gamepak_backup[fulladdr];
  }

  return value;
}

void function_cc write_backup(u32 address, u32 value) {
  value &= 0xFF;

  if (backup_type == BACKUP_EEPROM)
    return;

  if (backup_type == BACKUP_UNKN)
    backup_type = BACKUP_SRAM;

  // gamepak SRAM or Flash ROM
  if ((address == 0x5555) && (flash_mode != FLASH_WRITE_MODE)) {
    if((flash_command_position == 0) && (value == 0xAA)) {
      backup_type = BACKUP_FLASH;
      flash_command_position = 1;
    }

    if (flash_command_position == 2) {
      switch(value) {
        case 0x90:
          // Enter ID mode, this also tells the emulator that we're using
          // flash, not SRAM

          if(flash_mode == FLASH_BASE_MODE)
            flash_mode = FLASH_ID_MODE;

          break;

        case 0x80:
          // Enter erase mode
          if(flash_mode == FLASH_BASE_MODE)
            flash_mode = FLASH_ERASE_MODE;
          break;

        case 0xF0:
          // Terminate ID mode
          if(flash_mode == FLASH_ID_MODE)
            flash_mode = FLASH_BASE_MODE;
          break;

        case 0xA0:
          // Write mode
          if(flash_mode == FLASH_BASE_MODE)
            flash_mode = FLASH_WRITE_MODE;
          break;

        case 0xB0:
          // Bank switch
          // Here the chip is now officially 128KB.
          flash_bank_cnt = FLASH_SIZE_128KB;
          if(flash_mode == FLASH_BASE_MODE)
            flash_mode = FLASH_BANKSWITCH_MODE;
          break;

        case 0x10:
          // Erase chip
          if(flash_mode == FLASH_ERASE_MODE)
          {
            memset(gamepak_backup, 0xFF, 1024 * 128);
            flash_mode = FLASH_BASE_MODE;
          }
          break;

        default:
          break;
      }
      flash_command_position = 0;
    }
    if(backup_type == BACKUP_SRAM)
      gamepak_backup[0x5555] = value;
  }
  else if((address == 0x2AAA) && (value == 0x55) && (flash_command_position == 1))
    flash_command_position = 2;
  else {
    if((flash_command_position == 2) &&
     (flash_mode == FLASH_ERASE_MODE) && (value == 0x30))
    {
      // Erase sector
      u32 fulladdr = (address & 0xF000) + 64*1024*flash_bank_num;
      memset(&gamepak_backup[fulladdr], 0xFF, 1024 * 4);
      flash_mode = FLASH_BASE_MODE;
      flash_command_position = 0;
    }
    else if ((flash_command_position == 0) &&
             (flash_mode == FLASH_BANKSWITCH_MODE) && (address == 0x0000) &&
             (flash_bank_cnt == FLASH_SIZE_128KB)) {
      flash_bank_num = value & 1;
      flash_mode = FLASH_BASE_MODE;
    }
    else if((flash_command_position == 0) && (flash_mode == FLASH_WRITE_MODE)) {
      // Write value to flash ROM
      u32 fulladdr = address + 64*1024*flash_bank_num;
      gamepak_backup[fulladdr] = value;
      flash_mode = FLASH_BASE_MODE;
    }
    else if (backup_type == BACKUP_SRAM)
      gamepak_backup[address] = value;   // Write value to SRAM
  }
}

// EEPROM is 512 bytes by default; it is autodetected as 8KB if
// 14bit address DMAs are made (this is done in the DMA handler).

u32 eeprom_size = EEPROM_512_BYTE;
u32 eeprom_mode = EEPROM_BASE_MODE;
u32 eeprom_address = 0;
u32 eeprom_counter = 0;

u32 function_cc read_eeprom(void) {
  u32 value;

  switch(eeprom_mode) {
    case EEPROM_BASE_MODE:
      value = 1;
      break;

    case EEPROM_READ_MODE:
      value = (gamepak_backup[eeprom_address + (eeprom_counter / 8)] >>
       (7 - (eeprom_counter % 8))) & 0x01;
      eeprom_counter++;
      if(eeprom_counter == 64) {
        eeprom_counter = 0;
        eeprom_mode = EEPROM_BASE_MODE;
      }
      break;

    case EEPROM_READ_HEADER_MODE:
      value = 0;
      eeprom_counter++;
      if(eeprom_counter == 4) {
        eeprom_mode = EEPROM_READ_MODE;
        eeprom_counter = 0;
      }
      break;

    default:
      value = 0;
      break;
  }

  return value;
}

void function_cc write_eeprom(u32 unused_address, u32 value) {
  switch(eeprom_mode) {
    case EEPROM_BASE_MODE:
      backup_type = BACKUP_EEPROM;
      eeprom_address |= (value & 0x01) << (1 - eeprom_counter);
      if(++eeprom_counter == 2)
      {
        switch(eeprom_address & 0x03)
        {
          case 0x02:
            eeprom_mode = EEPROM_WRITE_ADDRESS_MODE;
            break;

          case 0x03:
            eeprom_mode = EEPROM_ADDRESS_MODE;
            break;
        }
        eeprom_counter = 0;
        eeprom_address = 0;
      }
      break;

    case EEPROM_ADDRESS_MODE:
    case EEPROM_WRITE_ADDRESS_MODE:
      eeprom_address |= (value & 0x01) << (15 - (eeprom_counter % 16));

      if(++eeprom_counter == (eeprom_size == EEPROM_512_BYTE ? 6 : 14))
      {
        eeprom_counter = 0;

        if (eeprom_size == EEPROM_512_BYTE)
          eeprom_address >>= 10;   // Addr is just 6 bits (drop 10LSB)
        else
          eeprom_address >>= 2;    // Addr is 14 bits (drop 2LSB)

        eeprom_address <<= 3;   // EEPROM accessed in blocks of 8 bytes

        if(eeprom_mode == EEPROM_ADDRESS_MODE)
          eeprom_mode = EEPROM_ADDRESS_FOOTER_MODE;
        else
        {
          eeprom_mode = EEPROM_WRITE_MODE;
          memset(gamepak_backup + eeprom_address, 0, 8);
        }
      }
      break;

    case EEPROM_WRITE_MODE:
      gamepak_backup[eeprom_address + (eeprom_counter / 8)] |=
       (value & 0x01) << (7 - (eeprom_counter % 8));
      eeprom_counter++;
      if(eeprom_counter == 64)
      {
        eeprom_counter = 0;
        eeprom_mode = EEPROM_WRITE_FOOTER_MODE;
      }
      break;

    case EEPROM_ADDRESS_FOOTER_MODE:
    case EEPROM_WRITE_FOOTER_MODE:
      eeprom_counter = 0;
      if(eeprom_mode == EEPROM_ADDRESS_FOOTER_MODE)
        eeprom_mode = EEPROM_READ_HEADER_MODE;
      else
        eeprom_mode = EEPROM_BASE_MODE;
      break;

    default:
      break;
  }
}

// General memory read codepath (only for aligned loads)
template<typename rdtype>
inline u32 read_memory(u32 address) {
  switch (address >> 24) {
    case 0x00:  // BIOS address space
      if (address >= 0x4000)
        return read_openbus<rdtype>(address);
      else if (reg[REG_PC] >= 0x4000)
        return (rdtype)(reg[REG_BUS_VALUE] >> ((address & 0x03) << 3));
      else
        return read_mem<rdtype>(bios_rom, address);
    case 0x02:  // EWRAM
      return read_mem<rdtype>(ewram, address & 0x3FFFF);
    case 0x03:  // IWRAM
      return read_mem<rdtype>(&iwram[0x8000], address & 0x7FFF);
    case 0x04:  // I/O registers
      return read_mem<rdtype>((u8*)io_registers, address & 0x3FF);
    case 0x05:  // Palette RAM
      return read_mem<rdtype>((u8*)palette_ram, address & 0x3FF);
    case 0x06:  // VRAM
      return read_mem<rdtype>(vram, vram_address(address));
    case 0x07:  // OAM RAM
      return read_mem<rdtype>((u8*)oam_ram, address & 0x3FF);

    case 0x0D:
      if (backup_type == BACKUP_EEPROM)
        return read_eeprom();
      /* fallthrough */
    case 0x08 ... 0x0C:  // Gamepak
      if ((address & 0x1FFFFFF) >= gamepak_size)
        return unmapped_rom_read<rdtype>(address);
      else {
        u32 rom_idx = address >> 15;
        u8 *map = memory_map_read[rom_idx];

        if (!map)
          map = load_gamepak_page(rom_idx & 0x3FF);

        return read_mem<rdtype>(map, address & 0x7FFF);
      }
    case 0x0E:
    case 0x0F:
      return read_backup<rdtype>(address);
    default:
      return read_openbus<rdtype>(address);
  };
}


static inline s32 signext28(u32 value) {
  s32 ret = (s32)(value << 4);
  return ret >> 4;
}

cpu_alert_type function_cc write_io_register16(u32 address, u32 value) {
  uint16_t ioreg = (address & 0x3FE) >> 1;
  value &= 0xffff;
  switch(ioreg) {
    case REG_DISPCNT:
      // Changing the lowest 3 bits might require object re-sorting
      reg[OAM_UPDATED] |= ((value & 0x07) != (read_ioreg(REG_DISPCNT) & 0x07));
      write_ioreg(REG_DISPCNT, value);
      break;

    // DISPSTAT has 3 read only bits, controlled by the LCD controller
    case REG_DISPSTAT:
      write_ioreg(REG_DISPSTAT, (read_ioreg(REG_DISPSTAT) & 0x07) | (value & ~0x07));
      break;

    // BG2 reference X
    case REG_BG2X_L:
    case REG_BG2X_H:
      write_ioreg(ioreg, value);
      affine_reference_x[0] = signext28(read_ioreg32(REG_BG2X_L));
      break;

    // BG2 reference Y
    case REG_BG2Y_L:
    case REG_BG2Y_H:
      write_ioreg(ioreg, value);
      affine_reference_y[0] = signext28(read_ioreg32(REG_BG2Y_L));
      break;

    // BG3 reference X
    case REG_BG3X_L:
    case REG_BG3X_H:
      write_ioreg(ioreg, value);
      affine_reference_x[1] = signext28(read_ioreg32(REG_BG3X_L));
      break;

    // BG3 reference Y
    case REG_BG3Y_L:
    case REG_BG3Y_H:
      write_ioreg(ioreg, value);
      affine_reference_y[1] = signext28(read_ioreg32(REG_BG3Y_L));
      break;

    // Sound 1 registers
    case REG_SOUND1CNT_L:    // control sweep
      iowrite_snd_tone_sweep(value);
      break;

    case REG_SOUND1CNT_H:    // control duty/length/envelope
      write_ioreg(REG_SOUND1CNT_H, iowrite_snd_tonectl_low(value, 0));
      break;

    case REG_SOUND1CNT_X:    // control frequency
      write_ioreg(REG_SOUND1CNT_X, iowrite_snd_tonectl_high(value, 0));
      break;

    // Sound 2 registers
    case REG_SOUND2CNT_L:    // control duty/length/envelope
      write_ioreg(REG_SOUND2CNT_L, iowrite_snd_tonectl_low(value, 1));
      break;

    case REG_SOUND2CNT_H:    // control frequency
      write_ioreg(REG_SOUND2CNT_H, iowrite_snd_tonectl_high(value, 1));
      break;

    // Sound 3 registers
    case REG_SOUND3CNT_L:    // control wave
      iowrite_snd_wavctl(value);
      break;

    case REG_SOUND3CNT_H:    // control length/volume
      iowrite_snd_tonectlwav_low(value);
      break;

    case REG_SOUND3CNT_X:    // control frequency
      iowrite_snd_tonectlwav_high(value);
      break;

    // Sound 4 registers
    case REG_SOUND4CNT_L:    // length/envelope
      write_ioreg(REG_SOUND4CNT_L, iowrite_snd_tonectl_low(value, 3));
      break;

    case REG_SOUND4CNT_H:    // control frequency
      iowrite_snd_noisectl(value);
      break;

    // Sound control registers
    case REG_SOUNDCNT_L:
      iowrite_sndctl_low(value);
      break;

    case REG_SOUNDCNT_H:
      iowrite_sndctl_high(value);
      break;

    case REG_SOUNDCNT_X:
      iowrite_sndctl_x(value);
      break;

    // Sound wave RAM, flag wave table update
    case REG_SOUNDWAVE_0 ... REG_SOUNDWAVE_7:
      iowrite_sndwav_tbl();
      write_ioreg(ioreg, value);
      break;

    // DMA control register: can cause an IRQ
    case REG_DMA0CNT_H: return iowrite_dma_cnt(0, value);
    case REG_DMA1CNT_H: return iowrite_dma_cnt(1, value);
    case REG_DMA2CNT_H: return iowrite_dma_cnt(2, value);
    case REG_DMA3CNT_H: return iowrite_dma_cnt(3, value);

    // Timer counter reload
    case REG_TM0D: iowrite_timer_reload(0, value); break;
    case REG_TM1D: iowrite_timer_reload(1, value); break;
    case REG_TM2D: iowrite_timer_reload(2, value); break;
    case REG_TM3D: iowrite_timer_reload(3, value); break;

    /* Timer control register (0..3)*/
    case REG_TM0CNT: iowrite_timer_cnt(0, value); break;
    case REG_TM1CNT: iowrite_timer_cnt(1, value); break;
    case REG_TM2CNT: iowrite_timer_cnt(2, value); break;
    case REG_TM3CNT: iowrite_timer_cnt(3, value); break;

    // Serial port registers
    case REG_SIOCNT:
      return write_siocnt(value);

    case REG_RCNT:
      return write_rcnt(value);

    // Interrupt flag, clears the bits it tries to write
    case REG_IF:
      write_ioreg(REG_IF, read_ioreg(REG_IF) & (~value));
      break;

    // Register writes with side-effects, can raise an IRQ
    case REG_IE:
    case REG_IME:
      write_ioreg(ioreg, value);
      return check_interrupt();

    // Read-only registers
    case REG_P1:
    case REG_VCOUNT:
      break;  // Do nothing

    case REG_WAITCNT:
      write_ioreg(REG_WAITCNT, value);
      reload_timing_info();
      break;

    // Registers without side effects
    default:
      write_ioreg(ioreg, value);
      break;
  }

  return CPU_ALERT_NONE;
}

cpu_alert_type function_cc write_io_register8(u32 address, u32 value) {
  if (address == 0x301) {
    if (value & 1)
      reg[CPU_HALT_STATE] = CPU_STOP;
    else
      reg[CPU_HALT_STATE] = CPU_HALT;
    return CPU_ALERT_HALT;
  }

  // Partial 16 bit write, treat like a regular merge-write
  if (address & 1)
    value = (value << 8) | (read_ioreg(address >> 1) & 0x00ff);
  else
    value = (value & 0xff) | (read_ioreg(address >> 1) & 0xff00);
  return write_io_register16(address & 0x3FE, value);
}

cpu_alert_type function_cc write_io_register32(u32 address, u32 value) {
  // Handle sound FIFO data write
  if (address == 0xA0) {
    sound_timer_queue32(0, value);
    return CPU_ALERT_NONE;
  }
  else if (address == 0xA4) {
    sound_timer_queue32(1, value);
    return CPU_ALERT_NONE;
  }

  // Perform two 16 bit writes. Low part goes first apparently.
  // Some Count+Control DMA writes use 32 bit, so control must be last.
  cpu_alert_type allow = write_io_register16(address, value & 0xFFFF);
  cpu_alert_type alhigh = write_io_register16(address + 2, value >> 16);
  return allow | alhigh;
}


// RTC code derived from VBA's (due to lack of any real publically available
// documentation...)

#define RTC_DISABLED                  0
#define RTC_IDLE                      1
#define RTC_COMMAND                   2
#define RTC_OUTPUT_DATA               3
#define RTC_INPUT_DATA                4

typedef enum
{
  RTC_COMMAND_RESET            = 0x60,
  RTC_COMMAND_WRITE_STATUS     = 0x62,
  RTC_COMMAND_READ_STATUS      = 0x63,
  RTC_COMMAND_OUTPUT_TIME_FULL = 0x65,
  RTC_COMMAND_OUTPUT_TIME      = 0x67
} rtc_command_type;

#define RTC_WRITE_TIME                0
#define RTC_WRITE_TIME_FULL           1
#define RTC_WRITE_STATUS              2

static bool rtc_enabled = false, rumble_enabled = false;

// I/O registers (for RTC, rumble, etc)
u8 gpio_regs[3];

// RTC tracking variables
u32 rtc_state = RTC_DISABLED;
u32 rtc_write_mode;
u32 rtc_command;
u64 rtc_data;
u32 rtc_data_bits;
u32 rtc_status = 0x40;
s32 rtc_bit_count;

// Rumble trackin vars, not really preserved (it's just aproximate)
static u32 rumble_enable_tick, rumble_ticks;

static u8 encode_bcd(u8 value)
{
  int l = 0;
  int h = 0;

  value = value % 100;
  l = value % 10;
  h = value / 10;

  return h * 16 + l;
}

void update_gpio_romregs() {
  if (rtc_enabled || rumble_enabled) {
    // Update the registers in the ROM mapped buffer.
    u8 *map = memory_map_read[0x8000000 >> 15];
    if (map) {
      if (gpio_regs[2]) {
        // Registers are visible, readable:
        write_mem<u16>(map, 0xC4, gpio_regs[0]);
        write_mem<u16>(map, 0xC6, gpio_regs[1]);
        write_mem<u16>(map, 0xC8, gpio_regs[2]);
      } else {
        // Registers are write-only, just read out zero
        write_mem<u16>(map, 0xC4, 0);
        write_mem<u16>(map, 0xC6, 0);
        write_mem<u16>(map, 0xC8, 0);
      }
    }
  }
}

#define GPIO_RTC_CLK   0x1
#define GPIO_RTC_DAT   0x2
#define GPIO_RTC_CSS   0x4

static void write_rtc(u8 oldv, u8 newv)
{
  // RTC works using a high CS and falling edge capture for the clock signal.
  if (!(newv & GPIO_RTC_CSS)) {
    // Chip select is down, reset the RTC protocol. And do not process input.
    rtc_state = RTC_IDLE;
    rtc_command = 0;
    rtc_bit_count = 0;
    return;
  }

  // CS low to high transition!
  if (!(oldv & GPIO_RTC_CSS))
    rtc_state = RTC_COMMAND;

  if ((oldv & GPIO_RTC_CLK) && !(newv & GPIO_RTC_CLK)) {
    // Advance clock state, input/ouput data.
    switch (rtc_state) {
    case RTC_COMMAND:
      rtc_command <<= 1;
      rtc_command |= ((newv >> 1) & 1);
      // 8 bit command read, process:
      if (++rtc_bit_count == 8) {
        switch (rtc_command) {
        case RTC_COMMAND_RESET:
        case RTC_COMMAND_WRITE_STATUS:
          rtc_state = RTC_INPUT_DATA;
          rtc_data = 0;
          rtc_data_bits = 8;
          rtc_write_mode = RTC_WRITE_STATUS;
          break;
        case RTC_COMMAND_READ_STATUS:
          rtc_state = RTC_OUTPUT_DATA;
          rtc_data_bits = 8;
          rtc_data = rtc_status;
          break;
        case RTC_COMMAND_OUTPUT_TIME_FULL:
          {
            struct tm *current_time;
            time_t current_time_flat;
            time(&current_time_flat);
            current_time = localtime(&current_time_flat);

            rtc_state = RTC_OUTPUT_DATA;
            rtc_data_bits = 56;
            rtc_data = ((u64)encode_bcd(current_time->tm_year)) |
                       ((u64)encode_bcd(current_time->tm_mon+1)<< 8) |
                       ((u64)encode_bcd(current_time->tm_mday) << 16) |
                       ((u64)encode_bcd(current_time->tm_wday) << 24) |
                       ((u64)encode_bcd(current_time->tm_hour) << 32) |
                       ((u64)encode_bcd(current_time->tm_min)  << 40) |
                       ((u64)encode_bcd(current_time->tm_sec)  << 48);
          }
          break;
        case RTC_COMMAND_OUTPUT_TIME:
          {
            struct tm *current_time;
            time_t current_time_flat;
            time(&current_time_flat);
            current_time = localtime(&current_time_flat);

            rtc_state = RTC_OUTPUT_DATA;
            rtc_data_bits = 24;
            rtc_data = (encode_bcd(current_time->tm_hour)) |
                       (encode_bcd(current_time->tm_min) << 8) |
                       (encode_bcd(current_time->tm_sec) << 16);
          }
          break;
        };
        rtc_bit_count = 0;
      }
      break;

    case RTC_INPUT_DATA:
      rtc_data <<= 1;
      rtc_data |= ((newv >> 1) & 1);
      rtc_data_bits--;
      if (!rtc_data_bits) {
        rtc_status = rtc_data; // HACK: assuming write status here.
        rtc_state = RTC_IDLE;
      }
      break;

    case RTC_OUTPUT_DATA:
      // Output the next bit from rtc_data
      if (!(gpio_regs[1] & 0x2)) {
        // Only output if the port is set to OUT!
        u32 bit = rtc_data & 1;
        gpio_regs[0] = (newv & ~0x2) | ((bit) << 1);
      }
      rtc_data >>= 1;
      rtc_data_bits--;

      if (!rtc_data_bits)
        rtc_state = RTC_IDLE;   // Finish transmission!

      break;
    };
  }
}

void write_rumble(bool oldv, bool newv) {
  if (newv && !oldv)
    rumble_enable_tick = cpu_ticks;
  else if (!newv && oldv) {
    rumble_ticks += (cpu_ticks - rumble_enable_tick);
    rumble_enable_tick = 0;
  }
}

void rumble_frame_reset() {
  // Reset the tick initial value to frame start (only if active)
  rumble_ticks = 0;
  if (rumble_enable_tick)
    rumble_enable_tick = cpu_ticks;
}

float rumble_active_pct() {
  // Calculate the percentage of Rumble active for this frame.
  u32 active_ticks = rumble_ticks;
  // If the rumble is still active, account for the due cycles
  if (rumble_enable_tick)
    active_ticks += (cpu_ticks - rumble_enable_tick);

  return active_ticks / (GBC_BASE_RATE / 60);
}

void function_cc write_gpio(u32 address, u32 value) {
  u8 prev_value = gpio_regs[0];
  switch(address) {
  case 0xC4:
    // Any writes do not affect input pins:
    gpio_regs[0] = (gpio_regs[0] & ~gpio_regs[1]) | (value & gpio_regs[1]);
    break;
  case 0xC6:
    gpio_regs[1] = value & 0xF;
    break;
  case 0xC8:   /* I/O port control */
    gpio_regs[2] = value & 1;
    break;
  };

  // If the game has an RTC, ensure it gets the data
  if (rtc_enabled && (prev_value & 0x7) != (gpio_regs[0] & 0x7))
    write_rtc(prev_value & 0x7, gpio_regs[0] & 0x7);

  if (rumble_enabled && (prev_value & 0x8) != (gpio_regs[0] & 0x8))
    write_rumble(prev_value & 0x8, gpio_regs[0] & 0x8);

  // Reflect the values
  update_gpio_romregs();
}

// EEPROM writes only happen in 16 bit mode
template <typename wrtype> inline cpu_alert_type write_eeprom(u32 value) {
  return CPU_ALERT_NONE;
}
template <> inline cpu_alert_type write_eeprom<u16>(u32 value) {
  write_eeprom(0, value);
  return CPU_ALERT_NONE;
}
// SRAM/FLASH can only be accessed using byte writes
template <typename wrtype> inline cpu_alert_type write_backup(u32 address, u32 value) {
  return CPU_ALERT_NONE;
}
template <> inline cpu_alert_type write_backup<u8>(u32 address, u32 value) {
  write_backup(address, value);
  return CPU_ALERT_NONE;
}
// OAM writes are not allowed at byte granularity
template <typename wrtype> inline cpu_alert_type oam_write(u32 address, u32 value) {
  write_mem<wrtype>((u8*)oam_ram, address & 0x3FF, value);
  return CPU_ALERT_NONE;
}
template <> inline cpu_alert_type oam_write<u8>(u32 address, u32 value) {
  return CPU_ALERT_NONE;
}
// GPIO writes are also 16 bit only
template <typename wrtype> inline cpu_alert_type gpio_write(u32 address, u32 value) {
  return CPU_ALERT_NONE;
}
template <> inline cpu_alert_type gpio_write<u16>(u32 address, u32 value) {
  write_gpio(address & 0xFF, value);
  return CPU_ALERT_NONE;
}


template<typename wrtype>
inline cpu_alert_type write_memory(u32 address, wrtype value) {
  switch (address >> 24) {
    case 0x02:  // EWRAM (checks for SMC)
      write_mem<wrtype>(ewram, address & 0x3FFFF, value);
      if (read_mem<wrtype>(&ewram[0x40000], address & 0x3FFFF))
        return CPU_ALERT_SMC;
      return CPU_ALERT_NONE;

    case 0x03:  // IWRAM (checks for SMC)
      write_mem<wrtype>(&iwram[0x8000], address & 0x7FFF, value);
      if (read_mem<wrtype>(iwram, address & 0x7FFF))
        return CPU_ALERT_SMC;
      return CPU_ALERT_NONE;

    case 0x04:  // I/O registers
      return write_ioregcb<wrtype>(address & 0x3FF, value);
    case 0x05:  // Palette RAM
      write_palette<wrtype>(address & 0x3FF, value);
      return CPU_ALERT_NONE;
    case 0x06:  // VRAM
      write_vram<wrtype>(vram_address(address), value);
      return CPU_ALERT_NONE;
    case 0x07:  // OAM RAM
      reg[OAM_UPDATED] = 1;
      return oam_write<wrtype>(address, value);
    case 0x08:  // GPIO mapped area
      return gpio_write<wrtype>(address, value);
    case 0x0D:  // EEPROM mapped area
      return write_eeprom<wrtype>(value);
    case 0x0E:  // FLASH/SRAM mapped area
      return write_backup<wrtype>(address & 0xFFFF, value);
    default:
      return CPU_ALERT_NONE;
  };
}

u32 function_cc read_memory8(u32 address) {
  return read_memory<u8>(address);
}

// unaligned reads are actually 32bit (rotated)
u32 function_cc read_memory16(u32 address) {
  u32 ret = read_memory<u16>(address & ~1U);
  if (address & 1)
    return rotr32(ret, 8);
  return ret;
}

u32 function_cc read_memory32(u32 address) {
  u32 ret = read_memory<u32>(address & ~3U);
  u32 rot = (address & 0x3) * 8;
  return rotr32(ret, rot);
}

u32 function_cc read_memory8s(u32 address) {
  return (u32)((s8)read_memory<u8>(address));
}

u32 function_cc read_memory16s(u32 address) {
  if (!(address & 1))
    return read_memory<u16>(address);

  s8 val = read_memory8s(address);
  return (u32)((s32)val);
}

cpu_alert_type function_cc write_memory8(u32 address, u8 value) {
  return write_memory<u8>(address, value);
}

cpu_alert_type function_cc write_memory16(u32 address, u16 value) {
  return write_memory<u16>(address, value);
}

cpu_alert_type function_cc write_memory32(u32 address, u32 value) {
  return write_memory<u32>(address, value);
}

typedef struct
{
   char gamepak_title[13];
   char gamepak_code[5];
   char gamepak_maker[3];
   u16 flags;
   u32 idle_loop_target_pc;
   u32 translation_gate_target_1;
   u32 translation_gate_target_2;
   u32 translation_gate_target_3;
} ini_t;

typedef struct
{
   char gamepak_title[13];
   char gamepak_code[5];
   char gamepak_maker[3];
} gamepak_info_t;

#define FLAGS_FLASH_128KB    0x0001   // Forces 128KB flash.
#define FLAGS_RUMBLE         0x0002   // Enables GPIO3 rumble support.
#define FLAGS_GBA_PLAYER     0x0004   // Enables GBA Player rumble support.
#define FLAGS_RTC            0x0008   // Enables RTC support by default.
#define FLAGS_EEPROM         0x0010   // Forces EEPROM storage.
#define FLAGS_RFU            0x0020   // Enables Wireless Adapter (via serial).

#include "gba_over.h"

static void load_game_config_over(gamepak_info_t *gpinfo) {
  for (unsigned i = 0; i < sizeof(gbaover)/sizeof(gbaover[0]); i++) {
     if (strcmp(gbaover[i].gamepak_code, gpinfo->gamepak_code))
        continue;

     if (strcmp(gbaover[i].gamepak_title, gpinfo->gamepak_title))
        continue;
     
     printf("gamepak title: %s\n", gbaover[i].gamepak_title);
     printf("gamepak code : %s\n", gbaover[i].gamepak_code);
     printf("gamepak maker: %s\n", gbaover[i].gamepak_maker);

     printf("INPUT gamepak title: %s\n", gpinfo->gamepak_title);
     printf("INPUT gamepak code : %s\n", gpinfo->gamepak_code);
     printf("INPUT gamepak maker: %s\n", gpinfo->gamepak_maker);

     if (gbaover[i].idle_loop_target_pc != 0)
        idle_loop_target_pc = gbaover[i].idle_loop_target_pc;

     if (gbaover[i].flags & FLAGS_FLASH_128KB) {
       flash_device_id = FLASH_DEVICE_MACRONIX_128KB;
       flash_bank_cnt = FLASH_SIZE_128KB;
     }

     if (gbaover[i].flags & FLAGS_RTC)
       rtc_enabled = true;

     if (gbaover[i].flags & FLAGS_RUMBLE)
       rumble_enabled = true;

     if (gbaover[i].flags & FLAGS_EEPROM)
       backup_type_reset = BACKUP_EEPROM;

     if (serial_mode == SERIAL_MODE_AUTO) {
       if (gbaover[i].flags & FLAGS_RFU)
         serial_mode = SERIAL_MODE_RFU;
       if (gbaover[i].flags & FLAGS_GBA_PLAYER)
         serial_mode = SERIAL_MODE_GBP;
     }

     if (gbaover[i].translation_gate_target_1 != 0)
     {
        translation_gate_target_pc[translation_gate_targets] = gbaover[i].translation_gate_target_1;
        translation_gate_targets++;
     }

     if (gbaover[i].translation_gate_target_2 != 0)
     {
        translation_gate_target_pc[translation_gate_targets] = gbaover[i].translation_gate_target_2;
        translation_gate_targets++;
     }

     if (gbaover[i].translation_gate_target_3 != 0)
     {
        translation_gate_target_pc[translation_gate_targets] = gbaover[i].translation_gate_target_3;
        translation_gate_targets++;
     }
  }
}

// Be sure to do this after loading ROMs.

#define map_rom_entry(type, idx, ptr, mirror_blocks) {                        \
  unsigned mcount;                                                            \
  for(mcount = 0; mcount < 1024; mcount += (mirror_blocks)) {                 \
    memory_map_##type[(0x8000000 / (32 * 1024)) + (idx) + mcount] = (ptr);    \
    memory_map_##type[(0xA000000 / (32 * 1024)) + (idx) + mcount] = (ptr);    \
  }                                                                           \
  for(mcount = 0; mcount <  512; mcount += (mirror_blocks)) {                 \
    memory_map_##type[(0xC000000 / (32 * 1024)) + (idx) + mcount] = (ptr);    \
  }                                                                           \
}

#define map_region(type, start, end, mirror_blocks, region)                   \
  for(map_offset = (start) / 0x8000; map_offset <                             \
   ((end) / 0x8000); map_offset++)                                            \
  {                                                                           \
    memory_map_##type[map_offset] =                                           \
     ((u8 *)region) + ((map_offset % mirror_blocks) * 0x8000);                \
  }                                                                           \

#define map_null(type, start, end) {                                          \
  u32 map_offset;                                                             \
  for(map_offset = start / 0x8000; map_offset < (end / 0x8000);               \
   map_offset++)                                                              \
    memory_map_##type[map_offset] = NULL;                                     \
}

#define map_vram(type)                                                        \
  for(map_offset = 0x6000000 / 0x8000; map_offset < (0x7000000 / 0x8000);     \
   map_offset += 4)                                                           \
  {                                                                           \
    memory_map_##type[map_offset] = vram;                                     \
    memory_map_##type[map_offset + 1] = vram + 0x8000;                        \
    memory_map_##type[map_offset + 2] = vram + (0x8000 * 2);                  \
    memory_map_##type[map_offset + 3] = vram + (0x8000 * 2);                  \
  }                                                                           \


static u32 evict_gamepak_page(void)
{
  u32 ret;
  s16 phyrom;
  do {
    // Return the index to the last used entry
    u32 newhead = gamepak_blk_queue[gamepak_lru_head].next_lru;
    phyrom = gamepak_blk_queue[gamepak_lru_head].phy_rom;
    ret = gamepak_lru_head;

    // Second elem becomes head now
    gamepak_lru_head = newhead;

    // The evicted element goes at the end of the queue
    gamepak_blk_queue[gamepak_lru_tail].next_lru = ret;
    gamepak_lru_tail = ret;
    // If this page is marked as sticky, we keep going through the list
  } while (phyrom >= 0 && gamepak_sb_test(phyrom));

  // We unmap the ROM page if it was mapped, ensure we do not access it
  // without triggering a "page fault"
  if (phyrom >= 0) {
    map_rom_entry(read, phyrom, NULL, gamepak_size >> 15);
  }

  return ret;
}

u8 *load_gamepak_page(u32 physical_index)
{
  if(physical_index >= (gamepak_size >> 15))
    return &gamepak_buffers[0][0];

  u32 entry = evict_gamepak_page();
  u32 block_idx = entry / 32;
  u32 block_off = entry % 32;
  u8 *swap_location = &gamepak_buffers[block_idx][32 * 1024 * block_off];

  // Fill in the entry
  gamepak_blk_queue[entry].phy_rom = physical_index;

  filestream_seek(gamepak_file_large, physical_index * (32 * 1024), SEEK_SET);
  filestream_read(gamepak_file_large, swap_location, (32 * 1024));

  // Map it to the read handlers now
  map_rom_entry(read, physical_index, swap_location, gamepak_size >> 15);

  // When mapping page 0, we might need to reflect the GPIO regs.
  if (physical_index == 0)
    update_gpio_romregs();

  return swap_location;
}

void init_gamepak_buffer(void) {
  // Try to allocate up to 32 blocks of 1MB each
  gamepak_buffer_count = 0;
  while (gamepak_buffer_count < ROM_BUFFER_SIZE)
  {
    void *ptr = malloc(gamepak_buffer_blocksize);
    if (!ptr)
      break;
    gamepak_buffers[gamepak_buffer_count++] = (u8*)ptr;
  }

  // Initialize the memory map structure
  for (unsigned i = 0; i < 1024; i++) {
    gamepak_blk_queue[i].next_lru = (u16)(i + 1);
    gamepak_blk_queue[i].phy_rom = -1;
  }

  gamepak_lru_head = 0;
  gamepak_lru_tail = 32 * gamepak_buffer_count - 1;
}

bool gamepak_must_swap(void)
{
  // Returns whether the current gamepak buffer is not big enough to hold
  // the full gamepak ROM. In these cases the device must swap.
  return gamepak_buffer_count * gamepak_buffer_blocksize < gamepak_size;
}

void init_memory(void)
{
  u32 map_offset = 0;

  // Reset DMA state
  init_dma();

  // Fill memory map regions, areas marked as NULL must be checked directly
  map_region(read, 0x0000000, 0x1000000, 1, bios_rom);
  map_null(read, 0x1000000, 0x2000000);
  map_region(read, 0x2000000, 0x3000000, 8, ewram);
  map_region(read, 0x3000000, 0x4000000, 1, &iwram[0x8000]);
  map_region(read, 0x4000000, 0x5000000, 1, io_registers);
  map_null(read, 0x5000000, 0x6000000);
  map_null(read, 0x6000000, 0x7000000);
  map_vram(read);
  map_null(read, 0x7000000, 0x8000000);
  map_null(read, 0xE000000, 0x10000000);

  memset(io_registers, 0, sizeof(io_registers));
  memset(oam_ram, 0, sizeof(oam_ram));
  memset(palette_ram, 0, sizeof(palette_ram));
  memset(iwram, 0, sizeof(iwram));
  memset(ewram, 0, sizeof(ewram));
  memset(vram, 0, sizeof(vram));

  write_ioreg(REG_DISPCNT, 0x80);
  write_ioreg(REG_P1, 0x3FF);
  write_ioreg(REG_BG2PA, 0x100);
  write_ioreg(REG_BG2PD, 0x100);
  write_ioreg(REG_BG3PA, 0x100);
  write_ioreg(REG_BG3PD, 0x100);
  write_ioreg(REG_RCNT, 0x8000);

  reload_timing_info();

  backup_type = backup_type_reset;
  flash_bank_num = 0;
  flash_command_position = 0;
  eeprom_size = EEPROM_512_BYTE;
  eeprom_mode = EEPROM_BASE_MODE;
  eeprom_address = 0;
  eeprom_counter = 0;
  rumble_enable_tick = 0;
  rumble_ticks = 0;

  flash_mode = FLASH_BASE_MODE;

  rtc_state = RTC_DISABLED;
  memset(gpio_regs, 0, sizeof(gpio_regs));
  reg[REG_BUS_VALUE] = 0xe129f000;
}

void memory_term(void)
{
  if (gamepak_file_large)
  {
    filestream_close(gamepak_file_large);
    gamepak_file_large = NULL;
  }

  while (gamepak_buffer_count)
  {
    free(gamepak_buffers[--gamepak_buffer_count]);
  }
}

bool memory_check_savestate(const u8 *src) {
  static const char *vars32[] = {
    "backup-type","flash-mode", "flash-cmd-pos", "flash-bank-num", "flash-dev-id",
    "flash-size", "eeprom-size", "eeprom-mode", "eeprom-addr", "eeprom-counter",
    "rtc-state", "rtc-write-mode", "rtc-cmd", "rtc-status", "rtc-data-bit-cnt", "rtc-bit-cnt",
  };
  const u8 *memdoc = bson_find_key(src, "memory");
  const u8 *bakdoc = bson_find_key(src, "backup");
  if (!memdoc || !bakdoc)
    return false;

  // Check memory buffers (TODO: check sizes!)
  if (!bson_contains_key(memdoc, "iwram", BSON_TYPE_BIN) ||
      !bson_contains_key(memdoc, "ewram", BSON_TYPE_BIN) ||
      !bson_contains_key(memdoc, "vram", BSON_TYPE_BIN) ||
      !bson_contains_key(memdoc, "oamram", BSON_TYPE_BIN) ||
      !bson_contains_key(memdoc, "palram", BSON_TYPE_BIN) ||
      !bson_contains_key(memdoc, "ioregs", BSON_TYPE_BIN) ||
      !bson_contains_key(memdoc, "dma-bus", BSON_TYPE_INT32))
     return false;

  // Check backup variables
  for (unsigned i = 0; i < sizeof(vars32)/sizeof(vars32[0]); i++)
    if (!bson_contains_key(bakdoc, vars32[i], BSON_TYPE_INT32))
      return false;

  if (!bson_contains_key(bakdoc, "gpio-regs", BSON_TYPE_BIN) ||
      !bson_contains_key(bakdoc, "rtc-data-words", BSON_TYPE_ARR))
      return false;

  return true;
}


bool memory_read_savestate(const u8 *src)
{
  u32 rtc_data_array[2];
  const u8 *memdoc = bson_find_key(src, "memory");
  const u8 *bakdoc = bson_find_key(src, "backup");
  if (!memdoc || !bakdoc)
    return false;

  if (!(
    bson_read_bytes(memdoc, "iwram", &iwram[0x8000], 0x8000) &&
    bson_read_bytes(memdoc, "ewram", ewram, 0x40000) &&
    bson_read_bytes(memdoc, "vram", vram, sizeof(vram)) &&
    bson_read_bytes(memdoc, "oamram", oam_ram, sizeof(oam_ram)) &&
    bson_read_bytes(memdoc, "palram", palette_ram, sizeof(palette_ram)) &&
    bson_read_bytes(memdoc, "ioregs", io_registers, sizeof(io_registers)) &&
    bson_read_int32(memdoc, "dma-bus", &dma_bus_val) &&

    bson_read_int32(bakdoc, "backup-type", &backup_type) &&

    bson_read_int32(bakdoc, "flash-mode", &flash_mode) &&
    bson_read_int32(bakdoc, "flash-cmd-pos", &flash_command_position) &&
    bson_read_int32(bakdoc, "flash-bank-num", &flash_bank_num) &&
    bson_read_int32(bakdoc, "flash-dev-id", &flash_device_id) &&
    bson_read_int32(bakdoc, "flash-size", &flash_bank_cnt) &&

    bson_read_int32(bakdoc, "eeprom-size", &eeprom_size) &&
    bson_read_int32(bakdoc, "eeprom-mode", &eeprom_mode) &&
    bson_read_int32(bakdoc, "eeprom-addr", &eeprom_address) &&
    bson_read_int32(bakdoc, "eeprom-counter", &eeprom_counter) &&

    bson_read_bytes(bakdoc, "gpio-regs", gpio_regs, sizeof(gpio_regs)) &&

    bson_read_int32(bakdoc, "rtc-state", &rtc_state) &&
    bson_read_int32(bakdoc, "rtc-write-mode", &rtc_write_mode) &&
    bson_read_int32(bakdoc, "rtc-cmd", &rtc_command) &&
    bson_read_int32(bakdoc, "rtc-status", &rtc_status) &&
    bson_read_int32(bakdoc, "rtc-data-bit-cnt", &rtc_data_bits) &&
    bson_read_int32(bakdoc, "rtc-bit-cnt", (u32*)&rtc_bit_count) &&
    bson_read_int32_array(bakdoc, "rtc-data-words", rtc_data_array, 2)))
    return false;

  rtc_data = rtc_data_array[0] | (((u64)rtc_data_array[1]) << 32);

  return true;
}

unsigned memory_write_savestate(u8 *dst)
{
  u8 *wbptr, *startp = dst;
  u32 rtc_data_array[2] = { (u32)rtc_data, (u32)(rtc_data >> 32) };

  bson_start_document(dst, "memory", wbptr);
  bson_write_bytes(dst, "iwram", &iwram[0x8000], 0x8000);
  bson_write_bytes(dst, "ewram", ewram, 0x40000);
  bson_write_bytes(dst, "vram", vram, sizeof(vram));
  bson_write_bytes(dst, "oamram", oam_ram, sizeof(oam_ram));
  bson_write_bytes(dst, "palram", palette_ram, sizeof(palette_ram));
  bson_write_bytes(dst, "ioregs", io_registers, sizeof(io_registers));
  bson_write_int32(dst, "dma-bus", dma_bus_val);
  bson_finish_document(dst, wbptr);

  bson_start_document(dst, "backup", wbptr);
  bson_write_int32(dst, "backup-type", (u32)backup_type);

  bson_write_int32(dst, "flash-mode", flash_mode);
  bson_write_int32(dst, "flash-cmd-pos", flash_command_position);
  bson_write_int32(dst, "flash-bank-num", flash_bank_num);
  bson_write_int32(dst, "flash-dev-id", flash_device_id);
  bson_write_int32(dst, "flash-size", flash_bank_cnt);

  bson_write_int32(dst, "eeprom-size", eeprom_size);
  bson_write_int32(dst, "eeprom-mode", eeprom_mode);
  bson_write_int32(dst, "eeprom-addr", eeprom_address);
  bson_write_int32(dst, "eeprom-counter", eeprom_counter);

  bson_write_bytes(dst, "gpio-regs", gpio_regs, sizeof(gpio_regs));
  bson_write_int32(dst, "rtc-state", rtc_state);
  bson_write_int32(dst, "rtc-write-mode", rtc_write_mode);
  bson_write_int32(dst, "rtc-cmd", rtc_command);
  bson_write_int32(dst, "rtc-status", rtc_status);
  bson_write_int32(dst, "rtc-data-bit-cnt", rtc_data_bits);
  bson_write_int32(dst, "rtc-bit-cnt", rtc_bit_count);
  bson_write_int32array(dst, "rtc-data-words", rtc_data_array, 2);
  bson_finish_document(dst, wbptr);

  return (unsigned int)(dst - startp);
}

static s32 load_gamepak_raw(const char *name) {
  gamepak_file_large = filestream_open(name, RETRO_VFS_FILE_ACCESS_READ,
                                       RETRO_VFS_FILE_ACCESS_HINT_NONE);
  if(gamepak_file_large)
  {
    // Round size to 32KB pages
    gamepak_size = (u32)filestream_get_size(gamepak_file_large);
    gamepak_size = (gamepak_size + 0x7FFF) & ~0x7FFF;

    // Load stuff in 1MB chunks
    u32 buf_blocks = (gamepak_size + gamepak_buffer_blocksize-1) / (gamepak_buffer_blocksize);
    u32 rom_blocks = gamepak_size >> 15;
    u32 ldblks = buf_blocks < gamepak_buffer_count ?
                    buf_blocks : gamepak_buffer_count;

    // Unmap the ROM space since we will re-map it now
    map_null(read, 0x8000000, 0xD000000);

    // Proceed to read the whole ROM or as much as possible.
    for (unsigned i = 0; i < ldblks; i++)
    {
      // Load 1MB chunk and map it
      filestream_read(gamepak_file_large, gamepak_buffers[i], gamepak_buffer_blocksize);
      for (unsigned j = 0; j < 32 && i*32 + j < rom_blocks; j++)
      {
        u32 phyn = i*32 + j;
        u8* blkptr = &gamepak_buffers[i][32 * 1024 * j];
        u32 entry = evict_gamepak_page();
        gamepak_blk_queue[entry].phy_rom = phyn;
        // Map it to the read handlers now
        map_rom_entry(read, phyn, blkptr, rom_blocks);
      }
    } 

    return 0;
  }

  return -1;
}

u32 load_gamepak(const struct retro_game_info* info, const char *name,
                 int force_rtc, int force_rumble, int force_serial)
{
   gamepak_info_t gpinfo;

   if (load_gamepak_raw(name))
      return -1;

   // Buffer 0 always has the first 1MB chunk of the ROM
   memset(&gpinfo, 0, sizeof(gpinfo));
   memcpy(gpinfo.gamepak_title, &gamepak_buffers[0][0xA0], 12);
   memcpy(gpinfo.gamepak_code,  &gamepak_buffers[0][0xAC],  4);
   memcpy(gpinfo.gamepak_maker, &gamepak_buffers[0][0xB0],  2);

   idle_loop_target_pc = 0xFFFFFFFF;
   translation_gate_targets = 0;
   flash_device_id = FLASH_DEVICE_MACRONIX_64KB;
   flash_bank_cnt = FLASH_SIZE_64KB;
   rtc_enabled = false;
   rumble_enabled = false;
   backup_type_reset = BACKUP_UNKN;
   serial_mode = force_serial;

   load_game_config_over(&gpinfo);

   // Forced RTC / Rumble modes, override the autodetect logic.
   if (force_rtc != FEAT_AUTODETECT)
      rtc_enabled = (force_rtc == FEAT_ENABLE);
   if (force_rumble != FEAT_AUTODETECT)
      rumble_enabled = (force_rumble == FEAT_ENABLE);

   return 0;
}

s32 load_bios(char *name)
{
  RFILE *fd = filestream_open(name, RETRO_VFS_FILE_ACCESS_READ,
                              RETRO_VFS_FILE_ACCESS_HINT_NONE);

  if(!fd)
    return -1;

  filestream_read(fd, bios_rom, 0x4000);
  filestream_close(fd);
  return 0;
}

