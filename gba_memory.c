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

#include "common.h"
#include "streams/file_stream.h"

/* Sound */
#define gbc_sound_tone_control_low(channel, regn)                             \
{                                                                             \
  u32 initial_volume = (value >> 12) & 0x0F;                                  \
  u32 envelope_ticks = ((value >> 8) & 0x07) * 4;                             \
  gbc_sound_channel[channel].length_ticks = 64 - (value & 0x3F);              \
  gbc_sound_channel[channel].sample_table_idx = ((value >> 6) & 0x03);        \
  gbc_sound_channel[channel].envelope_direction = (value >> 11) & 0x01;       \
  gbc_sound_channel[channel].envelope_initial_volume = initial_volume;        \
  gbc_sound_channel[channel].envelope_volume = initial_volume;                \
  gbc_sound_channel[channel].envelope_initial_ticks = envelope_ticks;         \
  gbc_sound_channel[channel].envelope_ticks = envelope_ticks;                 \
  gbc_sound_channel[channel].envelope_status = (envelope_ticks != 0);         \
  gbc_sound_channel[channel].envelope_volume = initial_volume;                \
  gbc_sound_update = 1;                                                       \
  write_ioreg(regn, value);                                                   \
}                                                                             \

#define gbc_sound_tone_control_high(channel, regn)                            \
{                                                                             \
  u32 rate = value & 0x7FF;                                                   \
  gbc_sound_channel[channel].rate = rate;                                     \
  gbc_sound_channel[channel].frequency_step =                                 \
   float_to_fp16_16(((131072.0 / (2048 - rate)) * 8.0) / sound_frequency);    \
  gbc_sound_channel[channel].length_status = (value >> 14) & 0x01;            \
  if(value & 0x8000)                                                          \
  {                                                                           \
    gbc_sound_channel[channel].active_flag = 1;                               \
    gbc_sound_channel[channel].sample_index -= float_to_fp16_16(1.0 / 12.0);  \
    gbc_sound_channel[channel].envelope_ticks =                               \
     gbc_sound_channel[channel].envelope_initial_ticks;                       \
    gbc_sound_channel[channel].envelope_volume =                              \
     gbc_sound_channel[channel].envelope_initial_volume;                      \
  }                                                                           \
                                                                              \
  gbc_sound_update = 1;                                                       \
  write_ioreg(regn, value);                                                   \
}                                                                             \

#define gbc_sound_tone_control_sweep()                                        \
{                                                                             \
  u32 sweep_ticks = ((value >> 4) & 0x07) * 2;                                \
  gbc_sound_channel[0].sweep_shift = value & 0x07;                            \
  gbc_sound_channel[0].sweep_direction = (value >> 3) & 0x01;                 \
  gbc_sound_channel[0].sweep_status = (value != 8);                           \
  gbc_sound_channel[0].sweep_ticks = sweep_ticks;                             \
  gbc_sound_channel[0].sweep_initial_ticks = sweep_ticks;                     \
  gbc_sound_update = 1;                                                       \
  write_ioreg(REG_SOUND1CNT_L, value);                                        \
}                                                                             \

#define gbc_sound_wave_control()                                              \
{                                                                             \
  gbc_sound_channel[2].wave_type = (value >> 5) & 0x01;                       \
  gbc_sound_channel[2].wave_bank = (value >> 6) & 0x01;                       \
  gbc_sound_channel[2].master_enable = 0;                                     \
  if(value & 0x80)                                                            \
    gbc_sound_channel[2].master_enable = 1;                                   \
                                                                              \
  gbc_sound_update = 1;                                                       \
  write_ioreg(REG_SOUND3CNT_L, value);                                        \
}                                                                             \

static const u32 gbc_sound_wave_volume[4] = { 0, 16384, 8192, 4096 };

#define gbc_sound_tone_control_low_wave()                                     \
{                                                                             \
  gbc_sound_channel[2].length_ticks = 256 - (value & 0xFF);                   \
  if((value >> 15) & 0x01)                                                    \
    gbc_sound_channel[2].wave_volume = 12288;                                 \
  else                                                                        \
    gbc_sound_channel[2].wave_volume =                                        \
     gbc_sound_wave_volume[(value >> 13) & 0x03];                             \
  gbc_sound_update = 1;                                                       \
  write_ioreg(REG_SOUND3CNT_H, value);                                        \
}                                                                             \

#define gbc_sound_tone_control_high_wave()                                    \
{                                                                             \
  u32 rate = value & 0x7FF;                                                   \
  gbc_sound_channel[2].rate = rate;                                           \
  gbc_sound_channel[2].frequency_step =                                       \
   float_to_fp16_16((2097152.0 / (2048 - rate)) / sound_frequency);           \
  gbc_sound_channel[2].length_status = (value >> 14) & 0x01;                  \
  if(value & 0x8000)                                                          \
  {                                                                           \
    gbc_sound_channel[2].sample_index = 0;                                    \
    gbc_sound_channel[2].active_flag = 1;                                     \
  }                                                                           \
  gbc_sound_update = 1;                                                       \
  write_ioreg(REG_SOUND3CNT_X, value);                                        \
}                                                                             \

#define gbc_sound_noise_control()                                             \
{                                                                             \
  u32 dividing_ratio = value & 0x07;                                          \
  u32 frequency_shift = (value >> 4) & 0x0F;                                  \
  if(dividing_ratio == 0)                                                     \
  {                                                                           \
    gbc_sound_channel[3].frequency_step =                                     \
     float_to_fp16_16(1048576.0 / (1 << (frequency_shift + 1)) /              \
     sound_frequency);                                                        \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    gbc_sound_channel[3].frequency_step =                                     \
     float_to_fp16_16(524288.0 / (dividing_ratio *                            \
     (1 << (frequency_shift + 1))) / sound_frequency);                        \
  }                                                                           \
  gbc_sound_channel[3].noise_type = (value >> 3) & 0x01;                      \
  gbc_sound_channel[3].length_status = (value >> 14) & 0x01;                  \
  if(value & 0x8000)                                                          \
  {                                                                           \
    gbc_sound_channel[3].sample_index = 0;                                    \
    gbc_sound_channel[3].active_flag = 1;                                     \
    gbc_sound_channel[3].envelope_ticks =                                     \
     gbc_sound_channel[3].envelope_initial_ticks;                             \
    gbc_sound_channel[3].envelope_volume =                                    \
     gbc_sound_channel[3].envelope_initial_volume;                            \
  }                                                                           \
  gbc_sound_update = 1;                                                       \
  write_ioreg(REG_SOUND4CNT_H, value);                                        \
}                                                                             \

static void gbc_trigger_sound(u32 value)
{
   u32 channel;

   /* Trigger all 4 GBC sound channels */
   for (channel = 0; channel < 4; channel++)
   {
      gbc_sound_master_volume_right = value & 0x07;
      gbc_sound_master_volume_left = (value >> 4) & 0x07;
      gbc_sound_channel[channel].status =
        (((value >> (channel + 8)) & 0x1) | ((value >> (channel + 11)) & 0x3));
   }
   write_ioreg(REG_SOUNDCNT_L, value);
}

#define trigger_sound()                                                       \
{                                                                             \
  timer[0].direct_sound_channels =                                            \
      ((((value >> 10) & 0x01) == 0) | ((((value >> 14) & 0x01) == 0) << 1)); \
  timer[1].direct_sound_channels =                                            \
      ((((value >> 10) & 0x01) == 1) | ((((value >> 14) & 0x01) == 1) << 1)); \
  direct_sound_channel[0].volume_halve = ((~(value >> 2)) & 0x01);            \
  direct_sound_channel[0].status = ((value >> 8) & 0x03);                     \
  direct_sound_channel[1].volume_halve = ((~(value >> 3)) & 0x01);            \
  direct_sound_channel[1].status = ((value >> 12) & 0x03);                    \
  gbc_sound_master_volume = value & 0x03;                                     \
                                                                              \
  if((value >> 11) & 0x01)                                                    \
    sound_reset_fifo(0);                                                      \
  if((value >> 15) & 0x01)                                                    \
    sound_reset_fifo(1);                                                      \
  write_ioreg(REG_SOUNDCNT_H, value);                                         \
}                                                                             \

static void sound_control_x(u32 value)
{
   if (value & 0x80)
   {
      if (sound_on != 1)
         sound_on = 1;
   }
   else
   {
      u32 i;
      for (i = 0; i < 4; i++)
         gbc_sound_channel[i].active_flag = 0;
      sound_on = 0;
   }

   value = (value & 0xFFF0) | (read_ioreg(REG_SOUNDCNT_X) & 0x000F);
   write_ioreg(REG_SOUNDCNT_X, value);
}

#define sound_update_frequency_step(timer_number)                             \
  timer[timer_number].frequency_step =                                        \
   float_to_fp8_24((GBC_BASE_RATE / sound_frequency) / (timer_reload))        \

/* Main */
extern timer_type timer[4];
static const u32 prescale_table[] = { 0, 6, 8, 10 };

#define count_timer(timer_number)                                             \
  timer[timer_number].reload = 0x10000 - value;                               \
  if(timer_number < 2)                                                        \
  {                                                                           \
    u32 timer_reload =                                                        \
     timer[timer_number].reload << timer[timer_number].prescale;              \
    sound_update_frequency_step(timer_number);                                \
  }                                                                           \

#define adjust_sound_buffer(timer_number, channel)                            \
  if(timer[timer_number].direct_sound_channels & (0x01 << channel))           \
  {                                                                           \
    direct_sound_channel[channel].buffer_index =                              \
     (gbc_sound_buffer_index + buffer_adjust) % BUFFER_SIZE;                  \
  }                                                                           \

static void trigger_timer(u32 timer_number, u32 value)
{
   if (value & 0x80)
   {
      if(timer[timer_number].status == TIMER_INACTIVE)
      {
         u32 prescale = prescale_table[value & 0x03];
         u32 timer_reload = timer[timer_number].reload;

         if((value >> 2) & 0x01)
            timer[timer_number].status = TIMER_CASCADE;
         else
            timer[timer_number].status = TIMER_PRESCALE;

         timer[timer_number].prescale = prescale;
         timer[timer_number].irq = ((value >> 6) & 0x1);

         write_ioreg(REG_TM0D + (timer_number * 2), (u32)(-timer_reload));

         timer_reload <<= prescale;
         timer[timer_number].count = timer_reload;

         if(timer_reload < execute_cycles)
            execute_cycles = timer_reload;

         if(timer_number < 2)
         {
            u32 buffer_adjust =
               (u32)(((float)(cpu_ticks - gbc_sound_last_cpu_ticks) *
                        sound_frequency) / GBC_BASE_RATE) * 2;

            sound_update_frequency_step(timer_number);
            adjust_sound_buffer(timer_number, 0);
            adjust_sound_buffer(timer_number, 1);
         }
      }
   }
   else
   {
      if(timer[timer_number].status != TIMER_INACTIVE)
      {
         timer[timer_number].status = TIMER_INACTIVE;
      }
   }
   write_ioreg(REG_TM0CNT + (timer_number * 2), value);
}

// This table is configured for sequential access on system defaults

const u32 waitstate_cycles_sequential[16][3] =
{
  { 1, 1, 1 }, // BIOS
  { 1, 1, 1 }, // Invalid
  { 3, 3, 6 }, // EWRAM (default settings)
  { 1, 1, 1 }, // IWRAM
  { 1, 1, 1 }, // IO Registers
  { 1, 1, 2 }, // Palette RAM
  { 1, 1, 2 }, // VRAM
  { 1, 1, 2 }, // OAM
  { 3, 3, 6 }, // Gamepak (wait 0)
  { 3, 3, 6 }, // Gamepak (wait 0)
  { 5, 5, 9 }, // Gamepak (wait 1)
  { 5, 5, 9 }, // Gamepak (wait 1)
  { 9, 9, 17 }, // Gamepak (wait 2)
  { 9, 9, 17 }, // Gamepak (wait 2)
};

// Different settings for gamepak ws0-2 sequential (2nd) access

const u32 gamepak_waitstate_sequential[2][3][3] =
{
  {
    { 3, 3, 6 },
    { 5, 5, 9 },
    { 9, 9, 17 }
  },
  {
    { 2, 2, 3 },
    { 2, 2, 3 },
    { 2, 2, 3 }
  }
};

u8 bios_rom[1024 * 16];
u32 bios_read_protect;

// Up to 128kb, store SRAM, flash ROM, or EEPROM here.
u8 gamepak_backup[1024 * 128];

dma_transfer_type dma[4];

// ROM memory is allocated in blocks of 1MB to better map the native block
// mapping system. We will try to allocate 32 of them to allow loading
// ROMs up to 32MB, but we might fail on memory constrained systems.

u8 *gamepak_buffers[32];    /* Pointers to malloc'ed blocks */
u32 gamepak_buffer_count;   /* Value between 1 and 32 */
u32 gamepak_size;           /* Size of the ROM in bytes */

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

// If GBC audio is written to:
u32 gbc_sound_update = 0;

// If the GBC audio waveform is modified:
u32 gbc_sound_wave_update = 0;

// Keep it 32KB until the upper 64KB is accessed, then make it 64KB.

u32 backup_type = BACKUP_NONE;
u32 sram_bankcount = SRAM_SIZE_32KB;

u32 flash_mode = FLASH_BASE_MODE;
u32 flash_command_position = 0;
u32 flash_bank_num;  // 0 or 1
u32 flash_bank_cnt;

u32 flash_device_id = FLASH_DEVICE_MACRONIX_64KB;

u8 read_backup(u32 address)
{
  u8 value = 0;

  if(backup_type == BACKUP_NONE)
    backup_type = BACKUP_SRAM;

  if(backup_type == BACKUP_SRAM)
    value = gamepak_backup[address];
  else if(flash_mode == FLASH_ID_MODE)
  {
    if (flash_bank_cnt == FLASH_SIZE_128KB)
    {
      /* ID manufacturer type */
      if(address == 0x0000)
        value = FLASH_MANUFACTURER_MACRONIX;
      /* ID device type */
      else if(address == 0x0001)
        value = FLASH_DEVICE_MACRONIX_128KB;
    }
    else
    {
      /* ID manufacturer type */
      if(address == 0x0000)
        value = FLASH_MANUFACTURER_PANASONIC;
      /* ID device type */
      else if(address == 0x0001)
        value = FLASH_DEVICE_PANASONIC_64KB;
    }
  }
  else
  {
    u32 fulladdr = address + 64*1024*flash_bank_num;
    value = gamepak_backup[fulladdr];
  }

  return value;
}

#define read_backup8()                                                        \
  value = read_backup(address & 0xFFFF)                                       \

#define read_backup16()                                                       \
  value = 0                                                                   \

#define read_backup32()                                                       \
  value = 0                                                                   \


// EEPROM is 512 bytes by default; it is autodetecte as 8KB if
// 14bit address DMAs are made (this is done in the DMA handler).

u32 eeprom_size = EEPROM_512_BYTE;
u32 eeprom_mode = EEPROM_BASE_MODE;
u32 eeprom_address = 0;
u32 eeprom_counter = 0;

void function_cc write_eeprom(u32 unused_address, u32 value)
{
  switch(eeprom_mode)
  {
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

#define read_memory_gamepak(type)                                             \
  u32 gamepak_index = address >> 15;                                          \
  u8 *map = memory_map_read[gamepak_index];                                   \
                                                                              \
  if(!map)                                                                    \
    map = load_gamepak_page(gamepak_index & 0x3FF);                           \
                                                                              \
  value = readaddress##type(map, address & 0x7FFF)                            \

#define read_open8()                                                          \
  if(!(reg[REG_CPSR] & 0x20))                                                 \
    value = read_memory8(reg[REG_PC] + 4 + (address & 0x03));                 \
  else                                                                        \
    value = read_memory8(reg[REG_PC] + 2 + (address & 0x01))                  \

#define read_open16()                                                         \
  if(!(reg[REG_CPSR] & 0x20))                                                 \
    value = read_memory16(reg[REG_PC] + 4 + (address & 0x02));                \
  else                                                                        \
    value = read_memory16(reg[REG_PC] + 2)                                    \

#define read_open32()                                                         \
  if(!(reg[REG_CPSR] & 0x20))                                                 \
    value = read_memory32(reg[REG_PC] + 4);                                   \
  else                                                                        \
  {                                                                           \
    u32 current_instruction = read_memory16(reg[REG_PC] + 2);                 \
    value = current_instruction | (current_instruction << 16);                \
  }                                                                           \

u32 function_cc read_eeprom(void)
{
  u32 value;

  switch(eeprom_mode)
  {
    case EEPROM_BASE_MODE:
      value = 1;
      break;

    case EEPROM_READ_MODE:
      value = (gamepak_backup[eeprom_address + (eeprom_counter / 8)] >>
       (7 - (eeprom_counter % 8))) & 0x01;
      eeprom_counter++;
      if(eeprom_counter == 64)
      {
        eeprom_counter = 0;
        eeprom_mode = EEPROM_BASE_MODE;
      }
      break;

    case EEPROM_READ_HEADER_MODE:
      value = 0;
      eeprom_counter++;
      if(eeprom_counter == 4)
      {
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


#define read_memory(type)                                                     \
  switch(address >> 24)                                                       \
  {                                                                           \
    case 0x00:                                                                \
      /* BIOS */                                                              \
      if(reg[REG_PC] >= 0x4000)                                               \
        ror(value, bios_read_protect, (address & 0x03) << 3);                 \
      else                                                                    \
        value = readaddress##type(bios_rom, address & 0x3FFF);                \
      break;                                                                  \
                                                                              \
    case 0x02:                                                                \
      /* external work RAM */                                                 \
      value = readaddress##type(ewram, (address & 0x3FFFF));                  \
      break;                                                                  \
                                                                              \
    case 0x03:                                                                \
      /* internal work RAM */                                                 \
      value = readaddress##type(iwram, (address & 0x7FFF) + 0x8000);          \
      break;                                                                  \
                                                                              \
    case 0x04:                                                                \
      /* I/O registers */                                                     \
      value = readaddress##type(io_registers, address & 0x3FF);               \
      break;                                                                  \
                                                                              \
    case 0x05:                                                                \
      /* palette RAM */                                                       \
      value = readaddress##type(palette_ram, address & 0x3FF);                \
      break;                                                                  \
                                                                              \
    case 0x06:                                                                \
      /* VRAM */                                                              \
      address &= 0x1FFFF;                                                     \
      if(address >= 0x18000)                                                  \
        address -= 0x8000;                                                    \
                                                                              \
      value = readaddress##type(vram, address);                               \
      break;                                                                  \
                                                                              \
    case 0x07:                                                                \
      /* OAM RAM */                                                           \
      value = readaddress##type(oam_ram, address & 0x3FF);                    \
      break;                                                                  \
                                                                              \
    case 0x08:                                                                \
    case 0x09:                                                                \
    case 0x0A:                                                                \
    case 0x0B:                                                                \
    case 0x0C:                                                                \
      /* gamepak ROM */                                                       \
      if((address & 0x1FFFFFF) >= gamepak_size)                               \
        value = 0;                                                            \
      else                                                                    \
      {                                                                       \
        read_memory_gamepak(type);                                            \
      }                                                                       \
      break;                                                                  \
                                                                              \
    case 0x0D:                                                                \
      if((address & 0x1FFFFFF) < gamepak_size)                                \
      {                                                                       \
        read_memory_gamepak(type);                                            \
      }                                                                       \
      else                                                                    \
        value = read_eeprom();                                                \
                                                                              \
      break;                                                                  \
                                                                              \
    case 0x0E:                                                                \
    case 0x0F:                                                                \
      read_backup##type();                                                    \
      break;                                                                  \
                                                                              \
    default:                                                                  \
      read_open##type();                                                      \
      break;                                                                  \
  }                                                                           \

static cpu_alert_type trigger_dma(u32 dma_number, u32 value)
{
  if(value & 0x8000)
  {
    if(dma[dma_number].start_type == DMA_INACTIVE)
    {
      u32 start_type = ((value >> 12) & 0x03);
      u32 src_address = 0xFFFFFFF & (read_dmareg(REG_DMA0SAD, dma_number) |
                         (read_dmareg(REG_DMA0SAD + 1, dma_number) << 16));
      u32 dst_address = 0xFFFFFFF & (read_dmareg(REG_DMA0DAD, dma_number) |
                         (read_dmareg(REG_DMA0DAD + 1, dma_number) << 16));

      dma[dma_number].source_address = src_address;
      dma[dma_number].dest_address = dst_address;
      dma[dma_number].source_direction = ((value >>  7) & 3);
      dma[dma_number].repeat_type = ((value >> 9) & 0x01);
      dma[dma_number].start_type = start_type;
      dma[dma_number].irq = ((value >> 14) & 0x1);

      /* If it is sound FIFO DMA make sure the settings are a certain way */
      if((dma_number >= 1) && (dma_number <= 2) &&
       (start_type == DMA_START_SPECIAL))
      {
        dma[dma_number].length_type = DMA_32BIT;
        dma[dma_number].length = 4;
        dma[dma_number].dest_direction = DMA_FIXED;
        if(dst_address == 0x40000A4)
          dma[dma_number].direct_sound_channel = DMA_DIRECT_SOUND_B;
        else
          dma[dma_number].direct_sound_channel = DMA_DIRECT_SOUND_A;
      }
      else
      {
        u32 length = read_dmareg(REG_DMA0CNT_L, dma_number);

        if((dma_number == 3) && ((dst_address >> 24) == 0x0D) &&
         ((length & 0x1F) == 17))
          eeprom_size = EEPROM_8_KBYTE;

        if(dma_number < 3)
          length &= 0x3FFF;

        if(length == 0)
        {
          if(dma_number == 3)
            length = 0x10000;
          else
            length = 0x04000;
        }

        dma[dma_number].length = length;
        dma[dma_number].length_type = ((value >> 10) & 0x01);
        dma[dma_number].dest_direction = ((value >> 5) & 3);
      }

      write_dmareg(REG_DMA0CNT_H, dma_number, value);
      if(start_type == DMA_START_IMMEDIATELY)
        return dma_transfer(dma_number, NULL);
    }
  }
  else
  {
    dma[dma_number].start_type = DMA_INACTIVE;
    dma[dma_number].direct_sound_channel = DMA_NO_DIRECT_SOUND;
    write_dmareg(REG_DMA0CNT_H, dma_number, value);
  }

  return CPU_ALERT_NONE;
}


#define access_register8_high(address)                                        \
  value = (value << 8) | (address8(io_registers, address))                    \

#define access_register8_low(address)                                         \
  value = ((address8(io_registers, address + 1)) << 8) | value                \

#define access_register16_high(address)                                       \
  value = (value << 16) | (readaddress16(io_registers, address))              \

#define access_register16_low(address)                                        \
  value = ((readaddress16(io_registers, address + 2)) << 16) | value          \

cpu_alert_type function_cc write_io_register8(u32 address, u32 value)
{
  value &= 0xff;
  switch(address)
  {
    case 0x00:
    {
      u32 dispcnt = read_ioreg(REG_DISPCNT);

      if((value & 0x07) != (dispcnt & 0x07))
        reg[OAM_UPDATED] = 1;

      address8(io_registers, 0x00) = value;
      break;
    }

    // DISPSTAT (lower byte)
    case 0x04:
      address8(io_registers, 0x04) =
       (address8(io_registers, 0x04) & 0x07) | (value & ~0x07);
      break;

    // VCOUNT
    case 0x06:
    case 0x07:
      break;

    // BG2 reference X
    case 0x28:
      access_register8_low(0x28);
      access_register16_low(0x28);
      affine_reference_x[0] = (s32)(value << 4) >> 4;
      address32(io_registers, 0x28) = eswap32(value);
      break;

    case 0x29:
      access_register8_high(0x28);
      access_register16_low(0x28);
      affine_reference_x[0] = (s32)(value << 4) >> 4;
      address32(io_registers, 0x28) = eswap32(value);
      break;

    case 0x2A:
      access_register8_low(0x2A);
      access_register16_high(0x28);
      affine_reference_x[0] = (s32)(value << 4) >> 4;
      address32(io_registers, 0x28) = eswap32(value);
      break;

    case 0x2B:
      access_register8_high(0x2A);
      access_register16_high(0x28);
      affine_reference_x[0] = (s32)(value << 4) >> 4;
      address32(io_registers, 0x28) = eswap32(value);
      break;

    // BG2 reference Y
    case 0x2C:
      access_register8_low(0x2C);
      access_register16_low(0x2C);
      affine_reference_y[0] = (s32)(value << 4) >> 4;
      address32(io_registers, 0x2C) = eswap32(value);
      break;

    case 0x2D:
      access_register8_high(0x2C);
      access_register16_low(0x2C);
      affine_reference_y[0] = (s32)(value << 4) >> 4;
      address32(io_registers, 0x2C) = eswap32(value);
      break;

    case 0x2E:
      access_register8_low(0x2E);
      access_register16_high(0x2C);
      affine_reference_y[0] = (s32)(value << 4) >> 4;
      address32(io_registers, 0x2C) = eswap32(value);
      break;

    case 0x2F:
      access_register8_high(0x2E);
      access_register16_high(0x2C);
      affine_reference_y[0] = (s32)(value << 4) >> 4;
      address32(io_registers, 0x2C) = eswap32(value);
      break;

    // BG3 reference X
    case 0x38:
      access_register8_low(0x38);
      access_register16_low(0x38);
      affine_reference_x[1] = (s32)(value << 4) >> 4;
      address32(io_registers, 0x38) = eswap32(value);
      break;

    case 0x39:
      access_register8_high(0x38);
      access_register16_low(0x38);
      affine_reference_x[1] = (s32)(value << 4) >> 4;
      address32(io_registers, 0x38) = eswap32(value);
      break;

    case 0x3A:
      access_register8_low(0x3A);
      access_register16_high(0x38);
      affine_reference_x[1] = (s32)(value << 4) >> 4;
      address32(io_registers, 0x38) = eswap32(value);
      break;

    case 0x3B:
      access_register8_high(0x3A);
      access_register16_high(0x38);
      affine_reference_x[1] = (s32)(value << 4) >> 4;
      address32(io_registers, 0x38) = eswap32(value);
      break;

    // BG3 reference Y
    case 0x3C:
      access_register8_low(0x3C);
      access_register16_low(0x3C);
      affine_reference_y[1] = (s32)(value << 4) >> 4;
      address32(io_registers, 0x3C) = eswap32(value);
      break;

    case 0x3D:
      access_register8_high(0x3C);
      access_register16_low(0x3C);
      affine_reference_y[1] = (s32)(value << 4) >> 4;
      address32(io_registers, 0x3C) = eswap32(value);
      break;

    case 0x3E:
      access_register8_low(0x3E);
      access_register16_high(0x3C);
      affine_reference_y[1] = (s32)(value << 4) >> 4;
      address32(io_registers, 0x3C) = eswap32(value);
      break;

    case 0x3F:
      access_register8_high(0x3E);
      access_register16_high(0x3C);
      affine_reference_y[1] = (s32)(value << 4) >> 4;
      address32(io_registers, 0x3C) = eswap32(value);
      break;

    // Sound 1 control sweep
    case 0x60:
      access_register8_low(0x60);
      gbc_sound_tone_control_sweep();
      break;

    case 0x61:
      access_register8_low(0x60);
      gbc_sound_tone_control_sweep();
      break;

    // Sound 1 control duty/length/envelope
    case 0x62:
      access_register8_low(0x62);
      gbc_sound_tone_control_low(0, REG_SOUND1CNT_H);
      break;

    case 0x63:
      access_register8_high(0x62);
      gbc_sound_tone_control_low(0, REG_SOUND1CNT_H);
      break;

    // Sound 1 control frequency
    case 0x64:
      access_register8_low(0x64);
      gbc_sound_tone_control_high(0, REG_SOUND1CNT_X);
      break;

    case 0x65:
      access_register8_high(0x64);
      gbc_sound_tone_control_high(0, REG_SOUND1CNT_X);
      break;

    // Sound 2 control duty/length/envelope
    case 0x68:
      access_register8_low(0x68);
      gbc_sound_tone_control_low(1, REG_SOUND2CNT_L);
      break;

    case 0x69:
      access_register8_high(0x68);
      gbc_sound_tone_control_low(1, REG_SOUND2CNT_L);
      break;

    // Sound 2 control frequency
    case 0x6C:
      access_register8_low(0x6C);
      gbc_sound_tone_control_high(1, REG_SOUND2CNT_H);
      break;

    case 0x6D:
      access_register8_high(0x6C);
      gbc_sound_tone_control_high(1, REG_SOUND2CNT_H);
      break;

    // Sound 3 control wave
    case 0x70:
      access_register8_low(0x70);
      gbc_sound_wave_control();
      break;

    case 0x71:
      access_register8_high(0x70);
      gbc_sound_wave_control();
      break;

    // Sound 3 control length/volume
    case 0x72:
      access_register8_low(0x72);
      gbc_sound_tone_control_low_wave();
      break;

    case 0x73:
      access_register8_high(0x72);
      gbc_sound_tone_control_low_wave();
      break;

    // Sound 3 control frequency
    case 0x74:
      access_register8_low(0x74);
      gbc_sound_tone_control_high_wave();
      break;

    case 0x75:
      access_register8_high(0x74);
      gbc_sound_tone_control_high_wave();
      break;

    // Sound 4 control length/envelope
    case 0x78:
      access_register8_low(0x78);
      gbc_sound_tone_control_low(3, REG_SOUND4CNT_L);
      break;

    case 0x79:
      access_register8_high(0x78);
      gbc_sound_tone_control_low(3, REG_SOUND4CNT_L);
      break;

    // Sound 4 control frequency
    case 0x7C:
      access_register8_low(0x7C);
      gbc_sound_noise_control();
      break;

    case 0x7D:
      access_register8_high(0x7C);
      gbc_sound_noise_control();
      break;

    // Sound control L
    case 0x80:
      access_register8_low(0x80);
      gbc_trigger_sound(value);
      break;

    case 0x81:
      access_register8_high(0x80);
      gbc_trigger_sound(value);
      break;

    // Sound control H
    case 0x82:
      access_register8_low(0x82);
      trigger_sound();
      break;

    case 0x83:
      access_register8_high(0x82);
      trigger_sound();
      break;

    // Sound control X
    case 0x84:
      sound_control_x(value);
      break;

    // Sound wave RAM
    case 0x90 ... 0x9F:
      gbc_sound_wave_update = 1;
      address8(io_registers, address) = value;
      break;

    // Sound FIFO A
    case 0xA0:
      sound_timer_queue8(0, value);
      break;

    // Sound FIFO B
    case 0xA4:
      sound_timer_queue8(1, value);
      break;

    // DMA control (trigger byte)
    case 0xBB:
      access_register8_low(0xBA);
      return trigger_dma(0, value);

    case 0xC7:
      access_register8_low(0xC6);
      return trigger_dma(1, value);

    case 0xD3:
      access_register8_low(0xD2);
      return trigger_dma(2, value);

    case 0xDF:
      access_register8_low(0xDE);
      return trigger_dma(3, value);

    // Timer counts
    case 0x100:
      access_register8_low(0x100);
      count_timer(0);
      break;

    case 0x101:
      access_register8_high(0x100);
      count_timer(0);
      break;

    case 0x104:
      access_register8_low(0x104);
      count_timer(1);
      break;

    case 0x105:
      access_register8_high(0x104);
      count_timer(1);
      break;

    case 0x108:
      access_register8_low(0x108);
      count_timer(2);
      break;

    case 0x109:
      access_register8_high(0x108);
      count_timer(2);
      break;

    case 0x10C:
      access_register8_low(0x10C);
      count_timer(3);
      break;

    case 0x10D:
      access_register8_high(0x10C);
      count_timer(3);
      break;

    // Timer control (trigger byte)
    case 0x103:
      access_register8_low(0x102);
      trigger_timer(0, value);
      break;

    case 0x107:
      access_register8_low(0x106);
      trigger_timer(1, value);
      break;

    case 0x10B:
      access_register8_low(0x10A);
      trigger_timer(2, value);
      break;

    case 0x10F:
      access_register8_low(0x10E);
      trigger_timer(3, value);
      break;

    // IF
    case 0x202:
      address8(io_registers, 0x202) &= ~value;
      break;

    case 0x203:
      address8(io_registers, 0x203) &= ~value;
      break;

    // Halt
    case 0x301:
      if((value & 0x01) == 0)
        reg[CPU_HALT_STATE] = CPU_HALT;
      else
        reg[CPU_HALT_STATE] = CPU_STOP;

      return CPU_ALERT_HALT;
      break;

    default:
      address8(io_registers, address) = value;
      break;
  }

  return CPU_ALERT_NONE;
}

cpu_alert_type function_cc write_io_register16(u32 address, u32 value)
{
  value &= 0xffff;
  switch(address)
  {
    case 0x00:
    {
      u32 dispcnt = read_ioreg(REG_DISPCNT);
      if((value & 0x07) != (dispcnt & 0x07))
        reg[OAM_UPDATED] = 1;

      write_ioreg(REG_DISPCNT, value);
      break;
    }

    // DISPSTAT
    case 0x04:
      write_ioreg(REG_DISPSTAT, (read_ioreg(REG_DISPSTAT) & 0x07) | (value & ~0x07));
      break;

    // VCOUNT
    case 0x06:
      break;

    // BG2 reference X
    case 0x28:
      access_register16_low(0x28);
      affine_reference_x[0] = (s32)(value << 4) >> 4;
      address32(io_registers, 0x28) = eswap32(value);
      break;

    case 0x2A:
      access_register16_high(0x28);
      affine_reference_x[0] = (s32)(value << 4) >> 4;
      address32(io_registers, 0x28) = eswap32(value);
      break;

    // BG2 reference Y
    case 0x2C:
      access_register16_low(0x2C);
      affine_reference_y[0] = (s32)(value << 4) >> 4;
      address32(io_registers, 0x2C) = eswap32(value);
      break;

    case 0x2E:
      access_register16_high(0x2C);
      affine_reference_y[0] = (s32)(value << 4) >> 4;
      address32(io_registers, 0x2C) = eswap32(value);
      break;

    // BG3 reference X

    case 0x38:
      access_register16_low(0x38);
      affine_reference_x[1] = (s32)(value << 4) >> 4;
      address32(io_registers, 0x38) = eswap32(value);
      break;

    case 0x3A:
      access_register16_high(0x38);
      affine_reference_x[1] = (s32)(value << 4) >> 4;
      address32(io_registers, 0x38) = eswap32(value);
      break;

    // BG3 reference Y
    case 0x3C:
      access_register16_low(0x3C);
      affine_reference_y[1] = (s32)(value << 4) >> 4;
      address32(io_registers, 0x3C) = eswap32(value);
      break;

    case 0x3E:
      access_register16_high(0x3C);
      affine_reference_y[1] = (s32)(value << 4) >> 4;
      address32(io_registers, 0x3C) = eswap32(value);
      break;

    // Sound 1 control sweep
    case 0x60:
      gbc_sound_tone_control_sweep();
      break;

    // Sound 1 control duty/length/envelope
    case 0x62:
      gbc_sound_tone_control_low(0, REG_SOUND1CNT_H);
      break;

    // Sound 1 control frequency
    case 0x64:
      gbc_sound_tone_control_high(0, REG_SOUND1CNT_X);
      break;

    // Sound 2 control duty/length/envelope
    case 0x68:
      gbc_sound_tone_control_low(1, REG_SOUND2CNT_L);
      break;

    // Sound 2 control frequency
    case 0x6C:
      gbc_sound_tone_control_high(1, REG_SOUND2CNT_H);
      break;

    // Sound 3 control wave
    case 0x70:
      gbc_sound_wave_control();
      break;

    // Sound 3 control length/volume
    case 0x72:
      gbc_sound_tone_control_low_wave();
      break;

    // Sound 3 control frequency
    case 0x74:
      gbc_sound_tone_control_high_wave();
      break;

    // Sound 4 control length/envelope
    case 0x78:
      gbc_sound_tone_control_low(3, REG_SOUND4CNT_L);
      break;

    // Sound 4 control frequency
    case 0x7C:
      gbc_sound_noise_control();
      break;

    // Sound control L
    case 0x80:
      gbc_trigger_sound(value);
      break;

    // Sound control H
    case 0x82:
      trigger_sound();
      break;

    // Sound control X
    case 0x84:
      sound_control_x(value);
      break;

    // Sound wave RAM
    case 0x90 ... 0x9E:
      gbc_sound_wave_update = 1;
      address16(io_registers, address) = eswap16(value);
      break;

    // Sound FIFO A
    case 0xA0:
      sound_timer_queue16(0, value);
      break;

    // Sound FIFO B
    case 0xA4:
      sound_timer_queue16(1, value);
      break;

    // DMA control
    case 0xBA:
      return trigger_dma(0, value);

    case 0xC6:
      return trigger_dma(1, value);

    case 0xD2:
      return trigger_dma(2, value);

    case 0xDE:
      return trigger_dma(3, value);

    // Timer counts
    case 0x100:
      count_timer(0);
      break;

    case 0x104:
      count_timer(1);
      break;

    case 0x108:
      count_timer(2);
      break;

    case 0x10C:
      count_timer(3);
      break;

    /* Timer control 0 */
    case 0x102:
      trigger_timer(0, value);
      break;

    /* Timer control 1 */
    case 0x106:
      trigger_timer(1, value);
      break;

    /* Timer control 2 */
    case 0x10A:
      trigger_timer(2, value);
      break;

    /* Timer control 3 */
    case 0x10E:
      trigger_timer(3, value);
      break;

    // P1
    case 0x130:
      break;

    // Interrupt flag
    case 0x202:
      write_ioreg(REG_IF, read_ioreg(REG_IF) & (~value));
      break;

    // WAITCNT
    case 0x204:
      break;

    // Halt
    case 0x300:
      if(((value >> 8) & 0x01) == 0)
        reg[CPU_HALT_STATE] = CPU_HALT;
      else
        reg[CPU_HALT_STATE] = CPU_STOP;

      return CPU_ALERT_HALT;

    default:
      address16(io_registers, address) = eswap16(value);
      break;
  }

  return CPU_ALERT_NONE;
}


cpu_alert_type function_cc write_io_register32(u32 address, u32 value)
{
  switch(address)
  {
    // BG2 reference X
    case 0x28:
      affine_reference_x[0] = (s32)(value << 4) >> 4;
      address32(io_registers, 0x28) = eswap32(value);
      break;

    // BG2 reference Y
    case 0x2C:
      affine_reference_y[0] = (s32)(value << 4) >> 4;
      address32(io_registers, 0x2C) = eswap32(value);
      break;

    // BG3 reference X
    case 0x38:
      affine_reference_x[1] = (s32)(value << 4) >> 4;
      address32(io_registers, 0x38) = eswap32(value);
      break;

    // BG3 reference Y
    case 0x3C:
      affine_reference_y[1] = (s32)(value << 4) >> 4;
      address32(io_registers, 0x3C) = eswap32(value);
      break;

    // Sound FIFO A
    case 0xA0:
      sound_timer_queue32(0, value);
      break;

    // Sound FIFO B
    case 0xA4:
      sound_timer_queue32(1, value);
      break;

    default:
    {
      cpu_alert_type alert_low =
        write_io_register16(address, value & 0xFFFF);

      cpu_alert_type alert_high =
        write_io_register16(address + 2, value >> 16);

      if(alert_high)
        return alert_high;

      return alert_low;
    }
  }

  return CPU_ALERT_NONE;
}

#define write_palette8(address, value)                                        \
{                                                                             \
  u32 aladdr = address & ~1U;                                                 \
  u16 val16 = (value << 8) | value;                                           \
  address16(palette_ram, aladdr) = eswap16(val16);                            \
  address16(palette_ram_converted, aladdr) = convert_palette(val16);          \
}

#define write_palette16(address, value)                                       \
{                                                                             \
  u32 palette_address = address;                                              \
  address16(palette_ram, palette_address) = eswap16(value);                   \
  value = convert_palette(value);                                             \
  address16(palette_ram_converted, palette_address) = value;                  \
}                                                                             \

#define write_palette32(address, value)                                       \
{                                                                             \
  u32 palette_address = address;                                              \
  u32 value_high = value >> 16;                                               \
  u32 value_low = value & 0xFFFF;                                             \
  address32(palette_ram, palette_address) = eswap32(value);                   \
  value_high = convert_palette(value_high);                                   \
  address16(palette_ram_converted, palette_address + 2) = value_high;         \
  value_low = convert_palette(value_low);                                     \
  address16(palette_ram_converted, palette_address) = value_low;              \
}                                                                             \


void function_cc write_backup(u32 address, u32 value)
{
  value &= 0xFF;

  if(backup_type == BACKUP_NONE)
    backup_type = BACKUP_SRAM;


  // gamepak SRAM or Flash ROM
  if((address == 0x5555) && (flash_mode != FLASH_WRITE_MODE))
  {
    if((flash_command_position == 0) && (value == 0xAA))
    {
      backup_type = BACKUP_FLASH;
      flash_command_position = 1;
    }

    if(flash_command_position == 2)
    {
      switch(value)
      {
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
            memset(gamepak_backup, 0xFF, 1024 * 64 * flash_bank_cnt);
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
  else

  if((address == 0x2AAA) && (value == 0x55) &&
   (flash_command_position == 1))
    flash_command_position = 2;
  else
  {
    if((flash_command_position == 2) &&
     (flash_mode == FLASH_ERASE_MODE) && (value == 0x30))
    {
      // Erase sector
      u32 fulladdr = (address & 0xF000) + 64*1024*flash_bank_num;
      memset(&gamepak_backup[fulladdr], 0xFF, 1024 * 4);
      flash_mode = FLASH_BASE_MODE;
      flash_command_position = 0;
    }
    else

    if((flash_command_position == 0) &&
     (flash_mode == FLASH_BANKSWITCH_MODE) && (address == 0x0000) &&
     (flash_bank_cnt == FLASH_SIZE_128KB))
    {
      flash_bank_num = value & 1;
      flash_mode = FLASH_BASE_MODE;
    }
    else

    if((flash_command_position == 0) && (flash_mode == FLASH_WRITE_MODE))
    {
      // Write value to flash ROM
      u32 fulladdr = address + 64*1024*flash_bank_num;
      gamepak_backup[fulladdr] = value;
      flash_mode = FLASH_BASE_MODE;
    }
    else

    if(backup_type == BACKUP_SRAM)
    {
      // Write value to SRAM
      // Hit 64KB territory?
      if(address >= 0x8000)
        sram_bankcount = SRAM_SIZE_64KB;
      gamepak_backup[address] = value;
    }
  }
}

#define write_backup8()                                                       \
  write_backup(address & 0xFFFF, value)                                       \

#define write_backup16()                                                      \

#define write_backup32()                                                      \

#define write_vram8()                                                         \
  address &= ~0x01;                                                           \
  address16(vram, address) = eswap16((value << 8) | value)                    \

#define write_vram16()                                                        \
  address16(vram, address) = eswap16(value)                                   \

#define write_vram32()                                                        \
  address32(vram, address) = eswap32(value)                                   \

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

u32 rtc_state = RTC_DISABLED;
u32 rtc_write_mode;
u8 rtc_registers[3];
u32 rtc_command;
u32 rtc_data[12];
u32 rtc_status = 0x40;
u32 rtc_data_bytes;
s32 rtc_bit_count;

static u32 encode_bcd(u8 value)
{
  int l = 0;
  int h = 0;

  value = value % 100;
  l = value % 10;
  h = value / 10;

  return h * 16 + l;
}

// RTC writes need to reflect in the bytes [0xC4..0xC9] of the gamepak
#define write_rtc_register(index, _value)                                     \
  update_address = 0x80000C4 + (index * 2);                                   \
  rtc_registers[index] = _value;                                              \
  rtc_page_index = update_address >> 15;                                      \
  map = memory_map_read[rtc_page_index];                                      \
                                                                              \
  if(map) {                                                                   \
    address16(map, update_address & 0x7FFF) = eswap16(_value);                \
  }                                                                           \

void function_cc write_rtc(u32 address, u32 value)
{
  u32 rtc_page_index;
  u32 update_address;
  u8 *map;

  value &= 0xFFFF;

  switch(address)
  {
    // RTC command
    // Bit 0: SCHK, perform action
    // Bit 1: IO, input/output command data
    // Bit 2: CS, select input/output? If high make I/O write only
    case 0xC4:
      if(rtc_state == RTC_DISABLED)
        rtc_state = RTC_IDLE;
      if(!(rtc_registers[0] & 0x04))
        value = (rtc_registers[0] & 0x02) | (value & ~0x02);
      if(rtc_registers[2] & 0x01)
      {
        // To begin writing a command 1, 5 must be written to the command
        // registers.
        if((rtc_state == RTC_IDLE) && (rtc_registers[0] == 0x01) &&
         (value == 0x05))
        {
          // We're now ready to begin receiving a command.
          write_rtc_register(0, value);
          rtc_state = RTC_COMMAND;
          rtc_command = 0;
          rtc_bit_count = 7;
        }
        else
        {
          write_rtc_register(0, value);
          switch(rtc_state)
          {
            // Accumulate RTC command by receiving the next bit, and if we
            // have accumulated enough bits to form a complete command
            // execute it.
            case RTC_COMMAND:
              if(rtc_registers[0] & 0x01)
              {
                rtc_command |= ((value & 0x02) >> 1) << rtc_bit_count;
                rtc_bit_count--;
              }

              // Have we received a full RTC command? If so execute it.
              if(rtc_bit_count < 0)
              {
                switch(rtc_command)
                {
                  // Resets RTC
                  case RTC_COMMAND_RESET:
                    rtc_state = RTC_IDLE;
                    memset(rtc_registers, 0, sizeof(rtc_registers));
                    break;

                  // Sets status of RTC
                  case RTC_COMMAND_WRITE_STATUS:
                    rtc_state = RTC_INPUT_DATA;
                    rtc_data_bytes = 1;
                    rtc_write_mode = RTC_WRITE_STATUS;
                    break;

                  // Outputs current status of RTC
                  case RTC_COMMAND_READ_STATUS:
                    rtc_state = RTC_OUTPUT_DATA;
                    rtc_data_bytes = 1;
                    rtc_data[0] = rtc_status;
                    break;

                  // Actually outputs the time, all of it
                  case RTC_COMMAND_OUTPUT_TIME_FULL:
                  {
                    struct tm *current_time;
                    time_t current_time_flat;

                    time(&current_time_flat);
                    current_time = localtime(&current_time_flat);

                    rtc_state = RTC_OUTPUT_DATA;
                    rtc_data_bytes = 7;
                    rtc_data[0] = encode_bcd(current_time->tm_year);
                    rtc_data[1] = encode_bcd(current_time->tm_mon + 1);
                    rtc_data[2] = encode_bcd(current_time->tm_mday);
                    rtc_data[3] = encode_bcd(current_time->tm_wday);
                    rtc_data[4] = encode_bcd(current_time->tm_hour);
                    rtc_data[5] = encode_bcd(current_time->tm_min);
                    rtc_data[6] = encode_bcd(current_time->tm_sec);

                    break;
                  }

                  // Only outputs the current time of day.
                  case RTC_COMMAND_OUTPUT_TIME:
                  {
                    struct tm *current_time;
                    time_t current_time_flat;

                    time(&current_time_flat);
                    current_time = localtime(&current_time_flat);

                    rtc_state = RTC_OUTPUT_DATA;
                    rtc_data_bytes = 3;
                    rtc_data[0] = encode_bcd(current_time->tm_hour);
                    rtc_data[1] = encode_bcd(current_time->tm_min);
                    rtc_data[2] = encode_bcd(current_time->tm_sec);
                    break;
                  }
                }
                rtc_bit_count = 0;
              }
              break;

            // Receive parameters from the game as input to the RTC
            // for a given command. Read one bit at a time.
            case RTC_INPUT_DATA:
              // Bit 1 of parameter A must be high for input
              if(rtc_registers[1] & 0x02)
              {
                // Read next bit for input
                if(!(value & 0x01))
                {
                  rtc_data[rtc_bit_count >> 3] |=
                   ((value & 0x01) << (7 - (rtc_bit_count & 0x07)));
                }
                else
                {
                  rtc_bit_count++;

                  if(rtc_bit_count == (signed)(rtc_data_bytes * 8))
                  {
                    rtc_state = RTC_IDLE;
                    switch(rtc_write_mode)
                    {
                      case RTC_WRITE_STATUS:
                        rtc_status = rtc_data[0];
                        break;

                      default:
                        break;
                    }
                  }
                }
              }
              break;

            case RTC_OUTPUT_DATA:
              // Bit 1 of parameter A must be low for output
              if(!(rtc_registers[1] & 0x02))
              {
                // Write next bit to output, on bit 1 of parameter B
                if(!(value & 0x01))
                {
                  u8 current_output_byte = rtc_registers[2];

                  current_output_byte =
                   (current_output_byte & ~0x02) |
                   (((rtc_data[rtc_bit_count >> 3] >>
                   (rtc_bit_count & 0x07)) & 0x01) << 1);

                  write_rtc_register(0, current_output_byte);

                }
                else
                {
                  rtc_bit_count++;

                  if(rtc_bit_count == (signed)(rtc_data_bytes * 8))
                  {
                    rtc_state = RTC_IDLE;
                    memset(rtc_registers, 0, sizeof(rtc_registers));
                  }
                }
              }
              break;

            default:
              break;
          }
        }
      }
      else
      {
        write_rtc_register(2, value);
      }
      break;

    // Write parameter A
    case 0xC6:
      write_rtc_register(1, value);
      break;

    // Write parameter B
    case 0xC8:
      write_rtc_register(2, value);
      break;
  }
}

#define write_rtc8()                                                          \

#define write_rtc16()                                                         \
  write_rtc(address & 0xFF, value)                                            \

#define write_rtc32()                                                         \

#define write_memory(type)                                                    \
  switch(address >> 24)                                                       \
  {                                                                           \
    case 0x02:                                                                \
      /* external work RAM */                                                 \
      address##type(ewram, (address & 0x3FFFF)) = eswap##type(value);         \
      break;                                                                  \
                                                                              \
    case 0x03:                                                                \
      /* internal work RAM */                                                 \
      address##type(iwram, (address & 0x7FFF) + 0x8000) = eswap##type(value); \
      break;                                                                  \
                                                                              \
    case 0x04:                                                                \
      /* I/O registers */                                                     \
      return write_io_register##type(address & 0x3FF, value);                 \
                                                                              \
    case 0x05:                                                                \
      /* palette RAM */                                                       \
      write_palette##type(address & 0x3FF, value);                            \
      break;                                                                  \
                                                                              \
    case 0x06:                                                                \
      /* VRAM */                                                              \
      address &= 0x1FFFF;                                                     \
      if(address >= 0x18000)                                                  \
        address -= 0x8000;                                                    \
                                                                              \
      write_vram##type();                                                     \
      break;                                                                  \
                                                                              \
    case 0x07:                                                                \
      /* OAM RAM */                                                           \
      if (type != 8) {                                                        \
        reg[OAM_UPDATED] = 1;                                                 \
        address##type(oam_ram, address & 0x3FF) = eswap##type(value);         \
      }                                                                       \
      break;                                                                  \
                                                                              \
    case 0x08:                                                                \
      /* gamepak ROM or RTC */                                                \
      write_rtc##type();                                                      \
      break;                                                                  \
                                                                              \
    case 0x09:                                                                \
    case 0x0A:                                                                \
    case 0x0B:                                                                \
    case 0x0C:                                                                \
      /* gamepak ROM space */                                                 \
      break;                                                                  \
                                                                              \
    case 0x0D:                                                                \
      write_eeprom(address, value);                                           \
      break;                                                                  \
                                                                              \
    case 0x0E:                                                                \
      write_backup##type();                                                   \
      break;                                                                  \
  }                                                                           \

u32 function_cc read_memory8(u32 address)
{
  u8 value;
  read_memory(8);
  return value;
}

u32 function_cc read_memory8s(u32 address) {
  return (u32)((s8)read_memory8(address));
}

u16 function_cc read_memory16_signed(u32 address)
{
  u16 value;

  if(address & 0x01)
    return (s8)read_memory8(address);

  read_memory(16);

  return value;
}

u32 function_cc read_memory16s(u32 address) {
  return (u32)((s16)read_memory16_signed(address));
}

// unaligned reads are actually 32bit

u32 function_cc read_memory16(u32 address)
{
  u32 value;
  bool unaligned = (address & 0x01);
  address &= ~0x01;
  read_memory(16);
  if (unaligned) {
    ror(value, value, 8);
  }

  return value;
}


u32 function_cc read_memory32(u32 address)
{
  u32 value;
  u32 rotate = (address & 0x03) * 8;
  address &= ~0x03;
  read_memory(32);
  ror(value, value, rotate);
  return value;
}

cpu_alert_type function_cc write_memory8(u32 address, u8 value)
{
  write_memory(8);
  return CPU_ALERT_NONE;
}

cpu_alert_type function_cc write_memory16(u32 address, u16 value)
{
  write_memory(16);
  return CPU_ALERT_NONE;
}

cpu_alert_type function_cc write_memory32(u32 address, u32 value)
{
  write_memory(32);
  return CPU_ALERT_NONE;
}

char backup_filename[512];

u32 load_backup(char *name)
{
  RFILE *fd = filestream_open(name, RETRO_VFS_FILE_ACCESS_READ,
                              RETRO_VFS_FILE_ACCESS_HINT_NONE);

  if(fd)
  {
    int64_t backup_size = filestream_get_size(fd);

    filestream_read(fd, gamepak_backup, backup_size);
    filestream_close(fd);

    // The size might give away what kind of backup it is.
    switch(backup_size)
    {
      case 0x200:
        backup_type = BACKUP_EEPROM;
        eeprom_size = EEPROM_512_BYTE;
        break;

      case 0x2000:
        backup_type = BACKUP_EEPROM;
        eeprom_size = EEPROM_8_KBYTE;
        break;

      case 0x8000:
        backup_type = BACKUP_SRAM;
        sram_bankcount = SRAM_SIZE_32KB;
        break;

      // Could be either flash or SRAM, go with flash
      case 0x10000:
        backup_type = BACKUP_FLASH;
        sram_bankcount = SRAM_SIZE_64KB;
        break;

      case 0x20000:
        backup_type = BACKUP_FLASH;
        flash_bank_cnt = FLASH_SIZE_128KB;
        break;
    }
    return 1;
  }
  else
  {
    backup_type = BACKUP_NONE;
    memset(gamepak_backup, 0xFF, 1024 * 128);
  }

  return 0;
}

u32 save_backup(char *name)
{
  if(backup_type != BACKUP_NONE)
  {
    RFILE *fd = filestream_open(name, RETRO_VFS_FILE_ACCESS_WRITE,
                                RETRO_VFS_FILE_ACCESS_HINT_NONE);

    if(fd)
    {
      u32 backup_size = 0;

      switch(backup_type)
      {
        case BACKUP_SRAM:
          backup_size = 0x8000 * sram_bankcount;
          break;

        case BACKUP_FLASH:
          backup_size = 0x10000 * flash_bank_cnt;
          break;

        case BACKUP_EEPROM:
          backup_size = 0x200 * eeprom_size;
          break;

        default:
          break;
      }

      filestream_write(fd, gamepak_backup, backup_size);
      filestream_close(fd);
      return 1;
    }
  }

  return 0;
}

void update_backup(void)
{
  if (!use_libretro_save_method)
    save_backup(backup_filename);
}

#define CONFIG_FILENAME "game_config.txt"

static char *skip_spaces(char *line_ptr)
{
  while(*line_ptr == ' ')
    line_ptr++;

  return line_ptr;
}

static s32 parse_config_line(char *current_line, char *current_variable, char *current_value)
{
  char *line_ptr = current_line;
  char *line_ptr_new;

  if((current_line[0] == 0) || (current_line[0] == '#'))
    return -1;

  line_ptr_new = strchr(line_ptr, ' ');
  if(!line_ptr_new)
    return -1;

  *line_ptr_new = 0;
  strcpy(current_variable, line_ptr);
  line_ptr_new = skip_spaces(line_ptr_new + 1);

  if(*line_ptr_new != '=')
    return -1;

  line_ptr_new = skip_spaces(line_ptr_new + 1);
  strcpy(current_value, line_ptr_new);
  line_ptr_new = current_value + strlen(current_value) - 1;
  if(*line_ptr_new == '\n')
  {
    line_ptr_new--;
    *line_ptr_new = 0;
  }

  if(*line_ptr_new == '\r')
    *line_ptr_new = 0;

  return 0;
}

typedef struct
{
   char gamepak_title[13];
   char gamepak_code[5];
   char gamepak_maker[3];
   int flash_size;
   u32 flash_device_id;
   int save_type;
   int rtc_enabled;
   int mirroring_enabled;
   int use_bios;
   u32 idle_loop_target_pc;
   u32 iwram_stack_optimize;
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

#include "gba_over.h"

static s32 load_game_config_over(gamepak_info_t *gpinfo)
{
  unsigned i = 0;

  for (i = 0; i < sizeof(gbaover)/sizeof(gbaover[0]); i++)
  {
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

     iwram_stack_optimize = gbaover[i].iwram_stack_optimize;
     
     flash_device_id      = gbaover[i].flash_device_id;
     if (flash_device_id == FLASH_DEVICE_MACRONIX_128KB)
       flash_bank_cnt = FLASH_SIZE_128KB;

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

     printf("found entry in over ini file.\n");

     return 0;
  }

  return -1;
}

static s32 load_game_config(gamepak_info_t *gpinfo)
{
  char current_line[256];
  char current_variable[256];
  char current_value[256];
  char config_path[512];
  RFILE *config_file;

  sprintf(config_path, "%s" PATH_SEPARATOR "%s", main_path, CONFIG_FILENAME);

  printf("config_path is : %s\n", config_path);

  config_file = filestream_open(config_path, RETRO_VFS_FILE_ACCESS_READ,
                                RETRO_VFS_FILE_ACCESS_HINT_NONE);

  if(config_file)
  {
    while(filestream_gets(config_file, current_line, 256))
    {
      if(parse_config_line(current_line, current_variable, current_value)
       != -1)
      {
        if(strcmp(current_variable, "game_name") ||
         strcmp(current_value, gpinfo->gamepak_title))
          continue;

        if(!filestream_gets(config_file, current_line, 256) ||
         (parse_config_line(current_line, current_variable,
           current_value) == -1) ||
         strcmp(current_variable, "game_code") ||
         strcmp(current_value, gpinfo->gamepak_code))
          continue;

        if(!filestream_gets(config_file, current_line, 256) ||
         (parse_config_line(current_line, current_variable,
           current_value) == -1) ||
         strcmp(current_variable, "vender_code") ||
          strcmp(current_value, gpinfo->gamepak_maker))
          continue;

        while(filestream_gets(config_file, current_line, 256))
        {
          if(parse_config_line(current_line, current_variable, current_value)
           != -1)
          {
            if(!strcmp(current_variable, "game_name"))
            {
              filestream_close(config_file);
              return 0;
            }

            if(!strcmp(current_variable, "idle_loop_eliminate_target"))
               idle_loop_target_pc = strtol(current_value, NULL, 16);

            if(!strcmp(current_variable, "translation_gate_target"))
            {
               if(translation_gate_targets < MAX_TRANSLATION_GATES)
               {
                  translation_gate_target_pc[translation_gate_targets] =
                     strtol(current_value, NULL, 16);
                  translation_gate_targets++;
               }
            }

            if(!strcmp(current_variable, "iwram_stack_optimize") &&
                  !strcmp(current_value, "no\0")) /* \0 for broken toolchain workaround */
               iwram_stack_optimize = 0;

            if(!strcmp(current_variable, "flash_rom_type") &&
              !strcmp(current_value, "128KB"))
              flash_device_id = FLASH_DEVICE_MACRONIX_128KB;
          }
        }

        filestream_close(config_file);
        return 0;
      }
    }

    filestream_close(config_file);
  }

  printf("game config missing\n");
  return -1;
}

// DMA memory regions can be one of the following:
// IWRAM - 32kb offset from the contiguous iwram region.
// EWRAM - also contiguous but with self modifying code check mirror.
// VRAM - 96kb offset from the contiguous vram region, should take care
// Palette RAM - Converts palette entries when written to.
// OAM RAM - Sets OAM modified flag to true.
// I/O registers - Uses the I/O register function.
// of mirroring properly.
// Segmented RAM/ROM - a region >= 32kb, the translated address has to
//  be reloaded if it wraps around the limit (cartride ROM)
// Ext - should be handled by the memory read/write function.

// The following map determines the region of each (assumes DMA access
// is not done out of bounds)

typedef enum
{
  DMA_REGION_IWRAM,
  DMA_REGION_EWRAM,
  DMA_REGION_VRAM,
  DMA_REGION_PALETTE_RAM,
  DMA_REGION_OAM_RAM,
  DMA_REGION_IO,
  DMA_REGION_GAMEPAK,
  DMA_REGION_EXT,
  DMA_REGION_BIOS,
  DMA_REGION_NULL
} dma_region_type;

const dma_region_type dma_region_map[17] =
{
  DMA_REGION_BIOS,          // 0x00 - BIOS
  DMA_REGION_NULL,          // 0x01 - Nothing
  DMA_REGION_EWRAM,         // 0x02 - EWRAM
  DMA_REGION_IWRAM,         // 0x03 - IWRAM
  DMA_REGION_IO,            // 0x04 - I/O registers
  DMA_REGION_PALETTE_RAM,   // 0x05 - palette RAM
  DMA_REGION_VRAM,          // 0x06 - VRAM
  DMA_REGION_OAM_RAM,       // 0x07 - OAM RAM
  DMA_REGION_GAMEPAK,       // 0x08 - gamepak ROM
  DMA_REGION_GAMEPAK,       // 0x09 - gamepak ROM
  DMA_REGION_GAMEPAK,       // 0x0A - gamepak ROM
  DMA_REGION_GAMEPAK,       // 0x0B - gamepak ROM
  DMA_REGION_GAMEPAK,       // 0x0C - gamepak ROM
  DMA_REGION_EXT,           // 0x0D - EEPROM
  DMA_REGION_EXT,           // 0x0E - gamepak SRAM/flash ROM
  DMA_REGION_EXT,           // 0x0F - gamepak SRAM/flash ROM
  DMA_REGION_NULL           // 0x10 - Not possible (undefined?)
};

#define dma_print(src_op, dest_op, transfer_size, wb)                         \
  printf("dma from %x (%s) to %x (%s) for %x (%s) (%s) (%d) (pc %x)\n",       \
   src_ptr, #src_op, dest_ptr, #dest_op, length, #transfer_size, #wb,         \
   dma->irq, reg[15]);                                                        \

#define dma_smc_vars_src()                                                    \

#define dma_smc_vars_dest()                                                   \
  u32 smc_trigger = 0                                                         \

#define dma_vars_iwram(type)                                                  \
  dma_smc_vars_##type()                                                       \

#define dma_vars_ewram(type)                                                  \
  dma_smc_vars_##type()

#define dma_oam_ram_dest()                                                    \
  reg[OAM_UPDATED] = 1                                                        \

#define dma_vars_oam_ram(type)                                                \
  dma_oam_ram_##type()                                                        \

#define dma_vars_io(type)
#define dma_vars_vram(type)
#define dma_vars_palette_ram(type)
#define dma_vars_bios(type)
#define dma_vars_ext(type)

#define dma_oam_ram_src()

#define dma_segmented_load_src()                                              \
  memory_map_read[src_current_region]                                         \

#define dma_vars_gamepak(type)                                                \
  u32 type##_new_region;                                                      \
  u32 type##_current_region = type##_ptr >> 15;                               \
  u8 *type##_address_block = dma_segmented_load_##type();                     \
  if(type##_address_block == NULL)                                            \
  {                                                                           \
    if((type##_ptr & 0x1FFFFFF) >= gamepak_size)                              \
      break;                                                                  \
    type##_address_block = load_gamepak_page(type##_current_region & 0x3FF);  \
  }                                                                           \

#define dma_gamepak_check_region(type)                                        \
  type##_new_region = (type##_ptr >> 15);                                     \
  if(type##_new_region != type##_current_region)                              \
  {                                                                           \
    type##_current_region = type##_new_region;                                \
    type##_address_block = dma_segmented_load_##type();                       \
    if(type##_address_block == NULL)                                          \
    {                                                                         \
      type##_address_block =                                                  \
       load_gamepak_page(type##_current_region & 0x3FF);                      \
    }                                                                         \
  }                                                                           \

#define dma_read_iwram(type, transfer_size)                                   \
  read_value = readaddress##transfer_size(iwram + 0x8000, type##_ptr & 0x7FFF)\

#define dma_read_vram(type, transfer_size) {                                  \
  u32 rdaddr = type##_ptr & 0x1FFFF;                                          \
  if (rdaddr >= 0x18000) rdaddr -= 0x8000;                                    \
  read_value = readaddress##transfer_size(vram, rdaddr);                      \
}

#define dma_read_io(type, transfer_size)                                      \
  read_value = readaddress##transfer_size(io_registers, type##_ptr & 0x3FF)   \

#define dma_read_oam_ram(type, transfer_size)                                 \
  read_value = readaddress##transfer_size(oam_ram, type##_ptr & 0x3FF)        \

#define dma_read_palette_ram(type, transfer_size)                             \
  read_value = readaddress##transfer_size(palette_ram, type##_ptr & 0x3FF)    \

#define dma_read_ewram(type, transfer_size)                                   \
  read_value = readaddress##transfer_size(ewram, type##_ptr & 0x3FFFF)        \

#define dma_read_gamepak(type, transfer_size)                                 \
  dma_gamepak_check_region(type);                                             \
  read_value = readaddress##transfer_size(type##_address_block,               \
   type##_ptr & 0x7FFF)                                                       \

// DMAing from the BIOS is funny, just returns 0..

#define dma_read_bios(type, transfer_size)                                    \
  read_value = 0                                                              \

#define dma_read_ext(type, transfer_size)                                     \
  read_value = read_memory##transfer_size(type##_ptr)                         \

#define dma_write_iwram(type, transfer_size)                                  \
  address##transfer_size(iwram + 0x8000, type##_ptr & 0x7FFF) =               \
                                          eswap##transfer_size(read_value);   \
  smc_trigger |= address##transfer_size(iwram, type##_ptr & 0x7FFF)           \

#define dma_write_vram(type, transfer_size) {                                 \
  u32 wraddr = type##_ptr & 0x1FFFF;                                          \
  if (wraddr >= 0x18000) wraddr -= 0x8000;                                    \
  address##transfer_size(vram, wraddr) = eswap##transfer_size(read_value);    \
}

#define dma_write_io(type, transfer_size)                                     \
  write_io_register##transfer_size(type##_ptr & 0x3FF, read_value)            \

#define dma_write_oam_ram(type, transfer_size)                                \
  address##transfer_size(oam_ram, type##_ptr & 0x3FF) =                       \
                                  eswap##transfer_size(read_value)            \

#define dma_write_palette_ram(type, transfer_size)                            \
  write_palette##transfer_size(type##_ptr & 0x3FF, read_value)                \

#define dma_write_ext(type, transfer_size)                                    \
  write_memory##transfer_size(type##_ptr, read_value)                         \

#define dma_write_ewram(type, transfer_size)                                  \
  address##transfer_size(ewram, type##_ptr & 0x3FFFF) =                       \
                                  eswap##transfer_size(read_value);           \
  smc_trigger |= address##transfer_size(ewram,                                \
   (type##_ptr & 0x3FFFF) + 0x40000)                                          \

#define dma_epilogue_iwram()                                                  \
  if(smc_trigger)                                                             \
  {                                                                           \
    /* Special return code indicating to retranslate to the CPU code */       \
    return_value = CPU_ALERT_SMC;                                             \
  }                                                                           \

#define dma_epilogue_ewram()                                                  \
  if(smc_trigger)                                                             \
  {                                                                           \
    /* Special return code indicating to retranslate to the CPU code */       \
    return_value = CPU_ALERT_SMC;                                             \
  }                                                                           \

#define dma_epilogue_vram()                                                   \

#define dma_epilogue_io()                                                     \

#define dma_epilogue_oam_ram()                                                \

#define dma_epilogue_palette_ram()                                            \

#define dma_epilogue_GAMEPAK()                                                \

#define dma_epilogue_ext()                                                    \

#define print_line()                                                          \
  dma_print(src_op, dest_op, transfer_size, wb);                              \

#define dma_transfer_loop_region(src_region_type, dest_region_type, src_op,   \
 dest_op, transfer_size, wb)                                                  \
{                                                                             \
  dma_vars_##src_region_type(src);                                            \
  dma_vars_##dest_region_type(dest);                                          \
                                                                              \
  for(i = 0; i < length; i++)                                                 \
  {                                                                           \
    dma_read_##src_region_type(src, transfer_size);                           \
    dma_write_##dest_region_type(dest, transfer_size);                        \
    src_ptr += src_op;                                                        \
    dest_ptr += dest_op;                                                      \
  }                                                                           \
  dma->source_address = src_ptr;                                              \
  if (wb)                                                                     \
    dma->dest_address = dest_ptr;                                             \
  dma_epilogue_##dest_region_type();                                          \
  break;                                                                      \
}                                                                             \

#define dma_tf_loop_builder(transfer_size)                                    \
cpu_alert_type dma_tf_loop##transfer_size(                                    \
  u32 src_ptr, u32 dest_ptr, int src_strd, int dest_strd,                     \
  bool wb, u32 length, dma_transfer_type *dma)                                \
{                                                                             \
  u32 i;                                                                      \
  u32 read_value;                                                             \
  cpu_alert_type return_value = CPU_ALERT_NONE;                               \
  u32 src_region = src_ptr >> 24;                                             \
  u32 dest_region = dest_ptr >> 24;                                           \
  dma_region_type src_region_type = dma_region_map[src_region];               \
  dma_region_type dest_region_type = dma_region_map[dest_region];             \
                                                                              \
  switch(src_region_type | (dest_region_type << 4))                           \
  {                                                                           \
    case (DMA_REGION_BIOS | (DMA_REGION_IWRAM << 4)):                         \
      dma_transfer_loop_region(bios, iwram, src_strd, dest_strd,              \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_IWRAM | (DMA_REGION_IWRAM << 4)):                        \
      dma_transfer_loop_region(iwram, iwram, src_strd, dest_strd,             \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_EWRAM | (DMA_REGION_IWRAM << 4)):                        \
      dma_transfer_loop_region(ewram, iwram, src_strd, dest_strd,             \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_VRAM | (DMA_REGION_IWRAM << 4)):                         \
      dma_transfer_loop_region(vram, iwram, src_strd, dest_strd,              \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_PALETTE_RAM | (DMA_REGION_IWRAM << 4)):                  \
      dma_transfer_loop_region(palette_ram, iwram, src_strd, dest_strd,       \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_OAM_RAM | (DMA_REGION_IWRAM << 4)):                      \
      dma_transfer_loop_region(oam_ram, iwram, src_strd, dest_strd,           \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_IO | (DMA_REGION_IWRAM << 4)):                           \
      dma_transfer_loop_region(io, iwram, src_strd, dest_strd,                \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_GAMEPAK | (DMA_REGION_IWRAM << 4)):                      \
      dma_transfer_loop_region(gamepak, iwram, src_strd, dest_strd,           \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_EXT | (DMA_REGION_IWRAM << 4)):                          \
      dma_transfer_loop_region(ext, iwram, src_strd, dest_strd,               \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_BIOS | (DMA_REGION_EWRAM << 4)):                         \
      dma_transfer_loop_region(bios, ewram, src_strd, dest_strd,              \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_IWRAM | (DMA_REGION_EWRAM << 4)):                        \
      dma_transfer_loop_region(iwram, ewram, src_strd, dest_strd,             \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_EWRAM | (DMA_REGION_EWRAM << 4)):                        \
      dma_transfer_loop_region(ewram, ewram, src_strd, dest_strd,             \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_VRAM | (DMA_REGION_EWRAM << 4)):                         \
      dma_transfer_loop_region(vram, ewram, src_strd, dest_strd,              \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_PALETTE_RAM | (DMA_REGION_EWRAM << 4)):                  \
      dma_transfer_loop_region(palette_ram, ewram, src_strd, dest_strd,       \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_OAM_RAM | (DMA_REGION_EWRAM << 4)):                      \
      dma_transfer_loop_region(oam_ram, ewram, src_strd, dest_strd,           \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_IO | (DMA_REGION_EWRAM << 4)):                           \
      dma_transfer_loop_region(io, ewram, src_strd, dest_strd,                \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_GAMEPAK | (DMA_REGION_EWRAM << 4)):                      \
      dma_transfer_loop_region(gamepak, ewram, src_strd, dest_strd,           \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_EXT | (DMA_REGION_EWRAM << 4)):                          \
      dma_transfer_loop_region(ext, ewram, src_strd, dest_strd,               \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_BIOS | (DMA_REGION_VRAM << 4)):                          \
      dma_transfer_loop_region(bios, vram, src_strd, dest_strd,               \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_IWRAM | (DMA_REGION_VRAM << 4)):                         \
      dma_transfer_loop_region(iwram, vram, src_strd, dest_strd,              \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_EWRAM | (DMA_REGION_VRAM << 4)):                         \
      dma_transfer_loop_region(ewram, vram, src_strd, dest_strd,              \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_VRAM | (DMA_REGION_VRAM << 4)):                          \
      dma_transfer_loop_region(vram, vram, src_strd, dest_strd,               \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_PALETTE_RAM | (DMA_REGION_VRAM << 4)):                   \
      dma_transfer_loop_region(palette_ram, vram, src_strd, dest_strd,        \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_OAM_RAM | (DMA_REGION_VRAM << 4)):                       \
      dma_transfer_loop_region(oam_ram, vram, src_strd, dest_strd,            \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_IO | (DMA_REGION_VRAM << 4)):                            \
      dma_transfer_loop_region(io, vram, src_strd, dest_strd,                 \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_GAMEPAK | (DMA_REGION_VRAM << 4)):                       \
      dma_transfer_loop_region(gamepak, vram, src_strd, dest_strd,            \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_EXT | (DMA_REGION_VRAM << 4)):                           \
      dma_transfer_loop_region(ext, vram, src_strd, dest_strd,                \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_BIOS | (DMA_REGION_PALETTE_RAM << 4)):                   \
      dma_transfer_loop_region(bios, palette_ram, src_strd, dest_strd,        \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_IWRAM | (DMA_REGION_PALETTE_RAM << 4)):                  \
      dma_transfer_loop_region(iwram, palette_ram, src_strd, dest_strd,       \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_EWRAM | (DMA_REGION_PALETTE_RAM << 4)):                  \
      dma_transfer_loop_region(ewram, palette_ram, src_strd, dest_strd,       \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_VRAM | (DMA_REGION_PALETTE_RAM << 4)):                   \
      dma_transfer_loop_region(vram, palette_ram, src_strd, dest_strd,        \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_PALETTE_RAM | (DMA_REGION_PALETTE_RAM << 4)):            \
      dma_transfer_loop_region(palette_ram, palette_ram, src_strd, dest_strd, \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_OAM_RAM | (DMA_REGION_PALETTE_RAM << 4)):                \
      dma_transfer_loop_region(oam_ram, palette_ram, src_strd, dest_strd,     \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_IO | (DMA_REGION_PALETTE_RAM << 4)):                     \
      dma_transfer_loop_region(io, palette_ram, src_strd, dest_strd,          \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_GAMEPAK | (DMA_REGION_PALETTE_RAM << 4)):                \
      dma_transfer_loop_region(gamepak, palette_ram, src_strd, dest_strd,     \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_EXT | (DMA_REGION_PALETTE_RAM << 4)):                    \
      dma_transfer_loop_region(ext, palette_ram, src_strd, dest_strd,         \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_BIOS | (DMA_REGION_OAM_RAM << 4)):                       \
      dma_transfer_loop_region(bios, oam_ram, src_strd, dest_strd,            \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_IWRAM | (DMA_REGION_OAM_RAM << 4)):                      \
      dma_transfer_loop_region(iwram, oam_ram, src_strd, dest_strd,           \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_EWRAM | (DMA_REGION_OAM_RAM << 4)):                      \
      dma_transfer_loop_region(ewram, oam_ram, src_strd, dest_strd,           \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_VRAM | (DMA_REGION_OAM_RAM << 4)):                       \
      dma_transfer_loop_region(vram, oam_ram, src_strd, dest_strd,            \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_PALETTE_RAM | (DMA_REGION_OAM_RAM << 4)):                \
      dma_transfer_loop_region(palette_ram, oam_ram, src_strd, dest_strd,     \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_OAM_RAM | (DMA_REGION_OAM_RAM << 4)):                    \
      dma_transfer_loop_region(oam_ram, oam_ram, src_strd, dest_strd,         \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_IO | (DMA_REGION_OAM_RAM << 4)):                         \
      dma_transfer_loop_region(io, oam_ram, src_strd, dest_strd,              \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_GAMEPAK | (DMA_REGION_OAM_RAM << 4)):                    \
      dma_transfer_loop_region(gamepak, oam_ram, src_strd, dest_strd,         \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_EXT | (DMA_REGION_OAM_RAM << 4)):                        \
      dma_transfer_loop_region(ext, oam_ram, src_strd, dest_strd,             \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_BIOS | (DMA_REGION_IO << 4)):                            \
      dma_transfer_loop_region(bios, io, src_strd, dest_strd,                 \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_IWRAM | (DMA_REGION_IO << 4)):                           \
      dma_transfer_loop_region(iwram, io, src_strd, dest_strd,                \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_EWRAM | (DMA_REGION_IO << 4)):                           \
      dma_transfer_loop_region(ewram, io, src_strd, dest_strd,                \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_VRAM | (DMA_REGION_IO << 4)):                            \
      dma_transfer_loop_region(vram, io, src_strd, dest_strd,                 \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_PALETTE_RAM | (DMA_REGION_IO << 4)):                     \
      dma_transfer_loop_region(palette_ram, io, src_strd, dest_strd,          \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_OAM_RAM | (DMA_REGION_IO << 4)):                         \
      dma_transfer_loop_region(oam_ram, io, src_strd, dest_strd,              \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_IO | (DMA_REGION_IO << 4)):                              \
      dma_transfer_loop_region(io, io, src_strd, dest_strd,                   \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_GAMEPAK | (DMA_REGION_IO << 4)):                         \
      dma_transfer_loop_region(gamepak, io, src_strd, dest_strd,              \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_EXT | (DMA_REGION_IO << 4)):                             \
      dma_transfer_loop_region(ext, io, src_strd, dest_strd,                  \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_BIOS | (DMA_REGION_EXT << 4)):                           \
      dma_transfer_loop_region(bios, ext, src_strd, dest_strd,                \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_IWRAM | (DMA_REGION_EXT << 4)):                          \
      dma_transfer_loop_region(iwram, ext, src_strd, dest_strd,               \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_EWRAM | (DMA_REGION_EXT << 4)):                          \
      dma_transfer_loop_region(ewram, ext, src_strd, dest_strd,               \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_VRAM | (DMA_REGION_EXT << 4)):                           \
      dma_transfer_loop_region(vram, ext, src_strd, dest_strd,                \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_PALETTE_RAM | (DMA_REGION_EXT << 4)):                    \
      dma_transfer_loop_region(palette_ram, ext, src_strd, dest_strd,         \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_OAM_RAM | (DMA_REGION_EXT << 4)):                        \
      dma_transfer_loop_region(oam_ram, ext, src_strd, dest_strd,             \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_IO | (DMA_REGION_EXT << 4)):                             \
      dma_transfer_loop_region(io, ext, src_strd, dest_strd,                  \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_GAMEPAK | (DMA_REGION_EXT << 4)):                        \
      dma_transfer_loop_region(gamepak, ext, src_strd, dest_strd,             \
       transfer_size, wb);                                                    \
                                                                              \
    case (DMA_REGION_EXT | (DMA_REGION_EXT << 3)):                            \
      dma_transfer_loop_region(ext, ext, src_strd, dest_strd,                 \
       transfer_size, wb);                                                    \
  }                                                                           \
  return return_value;                                                        \
}                                                                             \

dma_tf_loop_builder(16);
dma_tf_loop_builder(32);

static const int dma_stride[4] = {1, -1, 0, 1};

static cpu_alert_type dma_transfer_copy(
  dma_transfer_type *dmach, u32 src_ptr, u32 dest_ptr, u32 length)
{
  if (dmach->source_direction < 3)
  {
    int dst_stride = dma_stride[dmach->dest_direction];
    int src_stride = dma_stride[dmach->source_direction];
    bool dst_wb = dmach->dest_direction < 3;

    if(dmach->length_type == DMA_16BIT)
       return dma_tf_loop16(src_ptr, dest_ptr, 2 * src_stride, 2 * dst_stride, dst_wb, length, dmach);
    else
       return dma_tf_loop32(src_ptr, dest_ptr, 4 * src_stride, 4 * dst_stride, dst_wb, length, dmach);
  }

  return CPU_ALERT_NONE;
}

cpu_alert_type dma_transfer(unsigned dma_chan, int *usedcycles)
{
  dma_transfer_type *dmach = &dma[dma_chan];
  u32 src_ptr = dmach->source_address & (
                   dmach->length_type == DMA_16BIT ? ~1U : ~3U);
  u32 dst_ptr = dmach->dest_address & (
                   dmach->length_type == DMA_16BIT ? ~1U : ~3U);
  cpu_alert_type ret = CPU_ALERT_NONE;
  u32 tfsizes = dmach->length_type == DMA_16BIT ? 1 : 2;
  u32 byte_length = dmach->length << tfsizes;

  // Divide the DMA transaction into up to three transactions depending on
  // the source and destination memory regions.
  u32 src_end = MIN(0x10000000, src_ptr + byte_length * dma_stride[dmach->source_direction]);
  u32 dst_end = MIN(0x10000000, dst_ptr + byte_length * dma_stride[dmach->dest_direction]);

  dma_region_type src_reg0 = dma_region_map[src_ptr >> 24];
  dma_region_type src_reg1 = dma_region_map[src_end >> 24];
  dma_region_type dst_reg0 = dma_region_map[dst_ptr >> 24];
  dma_region_type dst_reg1 = dma_region_map[dst_end >> 24];

  if (src_reg0 == src_reg1 && dst_reg0 == dst_reg1)
    ret = dma_transfer_copy(dmach, src_ptr, dst_ptr, byte_length >> tfsizes);
  else if (src_reg0 == src_reg1) {
    // Source stays within the region, dest crosses over
    u32 blen0 = dma_stride[dmach->dest_direction] < 0 ?
        dst_ptr & 0xFFFFFF : 0x1000000 - (dst_ptr & 0xFFFFFF);
    u32 src1 = src_ptr + blen0 * dma_stride[dmach->source_direction];
    u32 dst1 = dst_ptr + blen0 * dma_stride[dmach->dest_direction];
    ret = dma_transfer_copy(dmach, src_ptr, dst_ptr, blen0 >> tfsizes);
    ret = dma_transfer_copy(dmach, src1, dst1, (byte_length - blen0) >> tfsizes);
  }
  else if (dst_reg0 == dst_reg1) {
    // Dest stays within the region, source crosses over
    u32 blen0 = dma_stride[dmach->source_direction] < 0 ?
        src_ptr & 0xFFFFFF : 0x1000000 - (src_ptr & 0xFFFFFF);
    u32 src1 = src_ptr + blen0 * dma_stride[dmach->source_direction];
    u32 dst1 = dst_ptr + blen0 * dma_stride[dmach->dest_direction];
    ret = dma_transfer_copy(dmach, src_ptr, dst_ptr, blen0 >> tfsizes);
    ret = dma_transfer_copy(dmach, src1, dst1, (byte_length - blen0) >> tfsizes);
  }
  // TODO: We do not cover the three-region case, seems no game uses that?
  // Lucky Luke does cross dest region due to some off-by-one error.

  if((dmach->repeat_type == DMA_NO_REPEAT) ||
   (dmach->start_type == DMA_START_IMMEDIATELY))
  {
    u32 cntrl = read_dmareg(REG_DMA0CNT_H, dma_chan);
    write_dmareg(REG_DMA0CNT_H, dma_chan, cntrl & (~0x8000));
    dmach->start_type = DMA_INACTIVE;
  }

  if(dmach->irq)
  {
    raise_interrupt(IRQ_DMA0 << dma_chan);
    ret = CPU_ALERT_IRQ;
  }

  // This is an approximation for the most common case (no region cross)
  if (usedcycles)
    *usedcycles += dmach->length * (
       waitstate_cycles_sequential[src_ptr >> 24][tfsizes] +
       waitstate_cycles_sequential[dst_ptr >> 24][tfsizes]);

  return ret;
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

  // If RTC is active page the RTC register bytes so they can be read
  if ((rtc_state != RTC_DISABLED) && (physical_index == 0)) {
    address16(swap_location, 0xC4) = eswap16(rtc_registers[0]);
    address16(swap_location, 0xC6) = eswap16(rtc_registers[1]);
    address16(swap_location, 0xC8) = eswap16(rtc_registers[2]);
  }

  return swap_location;
}

void init_gamepak_buffer(void)
{
  unsigned i;
  // Try to allocate up to 32 blocks of 1MB each
  gamepak_buffer_count = 0;
  while (gamepak_buffer_count < ROM_BUFFER_SIZE)
  {
    void *ptr = malloc(1024*1024);
    if (!ptr)
      break;
    gamepak_buffers[gamepak_buffer_count++] = (u8*)ptr;
  }

  // Initialize the memory map structure
  for (i = 0; i < 1024; i++)
  {
    gamepak_blk_queue[i].next_lru = (u16)(i + 1);
    gamepak_blk_queue[i].phy_rom = -1;
  }

  gamepak_lru_head = 0;
  gamepak_lru_tail = 32 * gamepak_buffer_count - 1;
}

void init_memory(void)
{
  u32 map_offset = 0;

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

  backup_type = BACKUP_NONE;

  sram_bankcount = SRAM_SIZE_32KB;
  //flash_size = FLASH_SIZE_64KB;

  flash_bank_num = 0;
  flash_command_position = 0;
  eeprom_size = EEPROM_512_BYTE;
  eeprom_mode = EEPROM_BASE_MODE;
  eeprom_address = 0;
  eeprom_counter = 0;

  flash_mode = FLASH_BASE_MODE;

  rtc_state = RTC_DISABLED;
  memset(rtc_registers, 0, sizeof(rtc_registers));
  bios_read_protect = 0xe129f000;
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

bool memory_read_savestate(const u8 *src)
{
  int i;
  const u8 *memdoc = bson_find_key(src, "memory");
  const u8 *bakdoc = bson_find_key(src, "backup");
  const u8 *dmadoc = bson_find_key(src, "dma");
  if (!memdoc || !bakdoc || !dmadoc)
    return false;

  if (!(
    bson_read_bytes(memdoc, "iwram", &iwram[0x8000], 0x8000) &&
    bson_read_bytes(memdoc, "ewram", ewram, 0x40000) &&
    bson_read_bytes(memdoc, "vram", vram, sizeof(vram)) &&
    bson_read_bytes(memdoc, "oamram", oam_ram, sizeof(oam_ram)) &&
    bson_read_bytes(memdoc, "palram", palette_ram, sizeof(palette_ram)) &&
    bson_read_bytes(memdoc, "ioregs", io_registers, sizeof(io_registers)) &&

    bson_read_int32(bakdoc, "backup-type", &backup_type) &&
    bson_read_int32(bakdoc, "sram-size", &sram_bankcount) &&

    bson_read_int32(bakdoc, "flash-mode", &flash_mode) &&
    bson_read_int32(bakdoc, "flash-cmd-pos", &flash_command_position) &&
    bson_read_int32(bakdoc, "flash-bank-num", &flash_bank_num) &&
    bson_read_int32(bakdoc, "flash-dev-id", &flash_device_id) &&
    bson_read_int32(bakdoc, "flash-size", &flash_bank_cnt) &&

    bson_read_int32(bakdoc, "eeprom-size", &eeprom_size) &&
    bson_read_int32(bakdoc, "eeprom-mode", &eeprom_mode) &&
    bson_read_int32(bakdoc, "eeprom-addr", &eeprom_address) &&
    bson_read_int32(bakdoc, "eeprom-counter", &eeprom_counter) &&

    bson_read_int32(bakdoc, "rtc-state", &rtc_state) &&
    bson_read_int32(bakdoc, "rtc-write-mode", &rtc_write_mode) &&
    bson_read_int32(bakdoc, "rtc-cmd", &rtc_command) &&
    bson_read_int32(bakdoc, "rtc-status", &rtc_status) &&
    bson_read_int32(bakdoc, "rtc-data-byte-cnt", &rtc_data_bytes) &&
    bson_read_int32(bakdoc, "rtc-bit-cnt", (u32*)&rtc_bit_count) &&
    bson_read_bytes(bakdoc, "rtc-regs", rtc_registers, sizeof(rtc_registers)) &&
    bson_read_int32_array(bakdoc, "rtc-data-words", rtc_data,
                            sizeof(rtc_data)/sizeof(rtc_data[0]))))
    return false;

  for (i = 0; i < DMA_CHAN_CNT; i++)
  {
    char tname[2] = {'0' + i, 0};
    const u8 *dmastr = bson_find_key(dmadoc, tname);
    if (!(
      bson_read_int32(dmastr, "src-addr", &dma[i].source_address) &&
      bson_read_int32(dmastr, "dst-addr", &dma[i].dest_address) &&
      bson_read_int32(dmastr, "src-dir", &dma[i].source_direction) &&
      bson_read_int32(dmastr, "dst-dir", &dma[i].dest_direction) &&
      bson_read_int32(dmastr, "len", &dma[i].length) &&
      bson_read_int32(dmastr, "size", &dma[i].length_type) &&
      bson_read_int32(dmastr, "repeat", &dma[i].repeat_type) &&
      bson_read_int32(dmastr, "start", &dma[i].start_type) &&
      bson_read_int32(dmastr, "dsc", &dma[i].direct_sound_channel) &&
      bson_read_int32(dmastr, "irq", &dma[i].irq)))
      return false;
  }

  return true;
}

unsigned memory_write_savestate(u8 *dst)
{
  int i;
  u8 *wbptr, *wbptr2, *startp = dst;
  bson_start_document(dst, "memory", wbptr);
  bson_write_bytes(dst, "iwram", &iwram[0x8000], 0x8000);
  bson_write_bytes(dst, "ewram", ewram, 0x40000);
  bson_write_bytes(dst, "vram", vram, sizeof(vram));
  bson_write_bytes(dst, "oamram", oam_ram, sizeof(oam_ram));
  bson_write_bytes(dst, "palram", palette_ram, sizeof(palette_ram));
  bson_write_bytes(dst, "ioregs", io_registers, sizeof(io_registers));
  bson_finish_document(dst, wbptr);

  bson_start_document(dst, "backup", wbptr);
  bson_write_int32(dst, "backup-type", (u32)backup_type);
  bson_write_int32(dst, "sram-size", sram_bankcount);

  bson_write_int32(dst, "flash-mode", flash_mode);
  bson_write_int32(dst, "flash-cmd-pos", flash_command_position);
  bson_write_int32(dst, "flash-bank-num", flash_bank_num);
  bson_write_int32(dst, "flash-dev-id", flash_device_id);
  bson_write_int32(dst, "flash-size", flash_bank_cnt);

  bson_write_int32(dst, "eeprom-size", eeprom_size);
  bson_write_int32(dst, "eeprom-mode", eeprom_mode);
  bson_write_int32(dst, "eeprom-addr", eeprom_address);
  bson_write_int32(dst, "eeprom-counter", eeprom_counter);

  bson_write_int32(dst, "rtc-state", rtc_state);
  bson_write_int32(dst, "rtc-write-mode", rtc_write_mode);
  bson_write_int32(dst, "rtc-cmd", rtc_command);
  bson_write_int32(dst, "rtc-status", rtc_status);
  bson_write_int32(dst, "rtc-data-byte-cnt", rtc_data_bytes);
  bson_write_int32(dst, "rtc-bit-cnt", rtc_bit_count);
  bson_write_bytes(dst, "rtc-regs", rtc_registers, sizeof(rtc_registers));
  bson_write_int32array(dst, "rtc-data-words", rtc_data,
                          sizeof(rtc_data)/sizeof(rtc_data[0]));
  bson_finish_document(dst, wbptr);

  bson_start_document(dst, "dma", wbptr);
  for (i = 0; i < DMA_CHAN_CNT; i++)
  {
    char tname[2] = {'0' + i, 0};
    bson_start_document(dst, tname, wbptr2);
    bson_write_int32(dst, "src-addr", dma[i].source_address);
    bson_write_int32(dst, "dst-addr", dma[i].dest_address);
    bson_write_int32(dst, "src-dir", dma[i].source_direction);
    bson_write_int32(dst, "dst-dir", dma[i].dest_direction);
    bson_write_int32(dst, "len", dma[i].length);
    bson_write_int32(dst, "size", dma[i].length_type);
    bson_write_int32(dst, "repeat", dma[i].repeat_type);
    bson_write_int32(dst, "start", dma[i].start_type);
    bson_write_int32(dst, "dsc", dma[i].direct_sound_channel);
    bson_write_int32(dst, "irq", dma[i].irq);
    bson_finish_document(dst, wbptr2);
  }
  bson_finish_document(dst, wbptr);

  return (unsigned int)(dst - startp);
}

static s32 load_gamepak_raw(const char *name)
{
  unsigned i, j;
  gamepak_file_large = filestream_open(name, RETRO_VFS_FILE_ACCESS_READ,
                                       RETRO_VFS_FILE_ACCESS_HINT_NONE);
  if(gamepak_file_large)
  {
    // Round size to 32KB pages
    gamepak_size = (u32)filestream_get_size(gamepak_file_large);
    gamepak_size = (gamepak_size + 0x7FFF) & ~0x7FFF;

    // Load stuff in 1MB chunks
    u32 buf_blocks = (gamepak_size + 1024*1024-1) / (1024*1024);
    u32 rom_blocks = gamepak_size >> 15;
    u32 ldblks = buf_blocks < gamepak_buffer_count ?
                    buf_blocks : gamepak_buffer_count;

    // Unmap the ROM space since we will re-map it now
    map_null(read, 0x8000000, 0xD000000);

    // Proceed to read the whole ROM or as much as possible.
    for (i = 0; i < ldblks; i++)
    {
      // Load 1MB chunk and map it
      filestream_read(gamepak_file_large, gamepak_buffers[i], 1024*1024);
      for (j = 0; j < 32 && i*32 + j < rom_blocks; j++)
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

u32 load_gamepak(const struct retro_game_info* info, const char *name)
{
   char *p;
   char gamepak_filename[512];
   gamepak_info_t gpinfo;

   if (load_gamepak_raw(name))
      return -1;

   strncpy(gamepak_filename, name, sizeof(gamepak_filename));
   gamepak_filename[sizeof(gamepak_filename) - 1] = 0;

   p = strrchr(gamepak_filename, PATH_SEPARATOR_CHAR);
   if (p)
      p++;
   else
      p = gamepak_filename;

   snprintf(backup_filename, sizeof(backup_filename), "%s%c%s", save_path, PATH_SEPARATOR_CHAR, p);
   p = strrchr(backup_filename, '.');
   if (p)
      strcpy(p, ".sav");

   if (!use_libretro_save_method)
     load_backup(backup_filename);

   // Buffer 0 always has the first 1MB chunk of the ROM
   memset(&gpinfo, 0, sizeof(gpinfo));
   memcpy(gpinfo.gamepak_title, &gamepak_buffers[0][0xA0], 12);
   memcpy(gpinfo.gamepak_code,  &gamepak_buffers[0][0xAC],  4);
   memcpy(gpinfo.gamepak_maker, &gamepak_buffers[0][0xB0],  2);

   idle_loop_target_pc = 0xFFFFFFFF;
   iwram_stack_optimize = 1;
   translation_gate_targets = 0;
   flash_device_id = FLASH_DEVICE_MACRONIX_64KB;
   flash_bank_cnt = FLASH_SIZE_64KB;

   if ((load_game_config_over(&gpinfo)) < 0)
      load_game_config(&gpinfo);

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


