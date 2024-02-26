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

#ifndef SOUND_H
#define SOUND_H

#ifdef __cplusplus
extern "C" {
#endif

#define BUFFER_SIZE        (1 << 16)
#define BUFFER_SIZE_MASK   (BUFFER_SIZE - 1)

#define GBA_SOUND_FREQUENCY   (64 * 1024)

#ifdef OVERCLOCK_60FPS
  #define GBC_BASE_RATE ((float)(60 * 228 * (272+960)))
#else
  #define GBC_BASE_RATE ((float)(16 * 1024 * 1024))
#endif

#define DIRECT_SOUND_INACTIVE         0
#define DIRECT_SOUND_RIGHT            1
#define DIRECT_SOUND_LEFT             2
#define DIRECT_SOUND_LEFTRIGHT        3

typedef struct
{
   s8 fifo[32];
   u32 fifo_base;
   u32 fifo_top;
   fixed8_24 fifo_fractional;
   // The + 1 is to give some extra room for linear interpolation
   // when wrapping around.
   u32 buffer_index;
   u32 status;
   u32 volume_halve;
} direct_sound_struct;

#define GBC_SOUND_INACTIVE            0
#define GBC_SOUND_RIGHT               1
#define GBC_SOUND_LEFT                2
#define GBC_SOUND_LEFTRIGHT           3

extern direct_sound_struct direct_sound_channel[2];
extern u32 gbc_sound_buffer_index;
extern u32 gbc_sound_last_cpu_ticks;

extern const u32 sound_frequency;

void sound_timer_queue32(u32 channel, u32 value);
unsigned sound_timer(fixed8_24 frequency_step, u32 channel);
void sound_reset_fifo(u32 channel);
void render_gbc_sound();
void init_sound();

bool sound_check_savestate(const u8 *src);
unsigned sound_write_savestate(u8 *dst);
bool sound_read_savestate(const u8 *src);

u32 sound_read_samples(s16 *out, u32 frames);

// I/O write interface
void iowrite_sndctl_x(u32 value);
void iowrite_snd_noisectl(u32 value);
void iowrite_snd_tone_sweep(u32 value);
void iowrite_snd_wavctl(u32 value);
u32 iowrite_snd_tonectl_low(u32 value, u32 chnum);
u32 iowrite_snd_tonectl_high(u32 value, u32 chnum);
void iowrite_snd_tonectlwav_low(u32 value);
void iowrite_snd_tonectlwav_high(u32 value);
void iowrite_sndwav_tbl();
void iowrite_sndctl_low(u32 value);
void iowrite_sndctl_high(u32 value);

void reset_sound(void);

#ifdef __cplusplus
}
#endif

#endif
