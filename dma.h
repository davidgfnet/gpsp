/* gameplaySP
 *
 * Copyright (C) 2006 Exophase <exophase@gmail.com>
 * Copyright (C) 2023 David Guillen Fandos <david@davidgf.net>
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

#ifdef __cplusplus
extern "C" {
#endif

#define DMA_CHAN_CNT   4

#define DMA_START_IMMEDIATELY         0
#define DMA_START_VBLANK              1
#define DMA_START_HBLANK              2
#define DMA_START_SPECIAL             3
#define DMA_INACTIVE                  4

#define DMA_16BIT                     0
#define DMA_32BIT                     1

#define DMA_NO_REPEAT                 0
#define DMA_REPEAT                    1

#define DMA_INCREMENT                 0
#define DMA_DECREMENT                 1
#define DMA_FIXED                     2
#define DMA_RELOAD                    3

#define DMA_NO_IRQ                    0
#define DMA_TRIGGER_IRQ               1

#define DMA_DIRECT_SOUND_A            0
#define DMA_DIRECT_SOUND_B            1
#define DMA_NO_DIRECT_SOUND           2

// Resets DMA registers and state
void init_dma();

// Performs a DMA transfer for the specified channel.
cpu_alert_type dma_transfer(unsigned dma_chan, unsigned *cycles);

// Handles a DMA control register write (might trigger a DMA)
cpu_alert_type iowrite_dma_cnt(u32 dma_number, u32 value);

// Savestate handlers
bool memdma_check_savestate(const u8 *src);
bool memdma_read_savestate(const u8 *src);
unsigned memdma_write_savestate(u8 *dst);

typedef struct
{
  u32 source_address;
  u32 dest_address;
  u32 length;
  u32 repeat_type;
  u32 direct_sound_channel;
  u32 source_direction;
  u32 dest_direction;
  u32 length_type;
  u32 start_type;
  u32 irq;
} dma_transfer_type;

extern dma_transfer_type dma[DMA_CHAN_CNT];
extern u32 dma_bus_val;

#ifdef __cplusplus
}
#endif

