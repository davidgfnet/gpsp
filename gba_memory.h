/* gameplaySP
 *
 * Copyright (C) 2006 Exophase <exophase@gmail.com>
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

#ifndef MEMORY_H
#define MEMORY_H

#include "libretro.h"

#define FEAT_AUTODETECT  -1
#define FEAT_DISABLE      0
#define FEAT_ENABLE       1

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

u32 function_cc read_memory8(u32 address);
u32 function_cc read_memory8s(u32 address);
u32 function_cc read_memory16(u32 address);
u16 function_cc read_memory16_signed(u32 address);
u32 function_cc read_memory16s(u32 address);
u32 function_cc read_memory32(u32 address);
cpu_alert_type function_cc write_memory8(u32 address, u8 value);
cpu_alert_type function_cc write_memory16(u32 address, u16 value);
cpu_alert_type function_cc write_memory32(u32 address, u32 value);
cpu_alert_type function_cc write_io_register8 (u32 address, u32 value);
cpu_alert_type function_cc write_io_register16(u32 address, u32 value);
cpu_alert_type function_cc write_io_register32(u32 address, u32 value);
u32 function_cc read_eeprom(void);
void function_cc write_eeprom(u32 address, u32 value);
u8 read_backup(u32 address);
void function_cc write_backup(u32 address, u32 value);
void function_cc write_gpio(u32 address, u32 value);

void write_rumble(bool oldv, bool newv);
void rumble_frame_reset();
float rumble_active_pct();

/* EDIT: Shouldn't this be extern ?! */
extern const u32 def_seq_cycles[16][2];
/* Cycles can change depending on WAITCNT */
extern u8 ws_cyc_seq[16][2];
extern u8 ws_cyc_nseq[16][2];

extern u32 gamepak_size;
extern char gamepak_title[13];
extern char gamepak_code[5];
extern char gamepak_maker[3];
extern char gamepak_filename[512];

u8 *memory_region(u32 address, u32 *memory_limit);
u32 load_gamepak(const struct retro_game_info* info, const char *name,
                 int force_rtc, int force_rumble, int force_serial);
s32 load_bios(char *name);
void init_memory(void);
void init_gamepak_buffer(void);
bool gamepak_must_swap(void);
void memory_term(void);
u8 *load_gamepak_page(u32 physical_index);

extern u32 oam_update;

extern u8 open_gba_bios_rom[1024*16];
extern u16 palette_ram[512];
extern u16 oam_ram[512];
extern u16 palette_ram_converted[512];
extern u16 io_registers[512];
extern u8 vram[1024 * 96];
extern u8 bios_rom[1024 * 16];
// Double buffer used for SMC detection
extern u8 ewram[1024 * 256 * 2];
extern u8 iwram[1024 * 32 * 2];

extern u8 *memory_map_read[8 * 1024];

#define BACKUP_SRAM       0
#define BACKUP_FLASH      1
#define BACKUP_EEPROM     2
#define BACKUP_UNKN       3

#define SRAM_SIZE_32KB    1
#define SRAM_SIZE_64KB    2

#define FLASH_SIZE_64KB   1
#define FLASH_SIZE_128KB  2

#define EEPROM_512_BYTE   1
#define EEPROM_8_KBYTE   16

#define EEPROM_BASE_MODE              0
#define EEPROM_READ_MODE              1
#define EEPROM_READ_HEADER_MODE       2
#define EEPROM_ADDRESS_MODE           3
#define EEPROM_WRITE_MODE             4
#define EEPROM_WRITE_ADDRESS_MODE     5
#define EEPROM_ADDRESS_FOOTER_MODE    6
#define EEPROM_WRITE_FOOTER_MODE      7

#define FLASH_BASE_MODE               0
#define FLASH_ERASE_MODE              1
#define FLASH_ID_MODE                 2
#define FLASH_WRITE_MODE              3
#define FLASH_BANKSWITCH_MODE         4

extern u32 backup_type;
extern u32 sram_bankcount;
extern u32 flash_bank_cnt;
extern u32 eeprom_size;

extern u8 gamepak_backup[1024 * 128];

// Page sticky bit routines
extern u32 gamepak_sticky_bit[1024/32];
static inline void touch_gamepak_page(u32 physical_index)
{
  u32 idx = (physical_index >> 5) & 31;
  u32 bof = physical_index & 31;

  gamepak_sticky_bit[idx] |= (1 << bof);
}

static inline void clear_gamepak_stickybits(void)
{
  memset(gamepak_sticky_bit, 0, sizeof(gamepak_sticky_bit));
}

bool memory_check_savestate(const u8*src);
bool memory_read_savestate(const u8*src);
unsigned memory_write_savestate(u8 *dst);

#endif
