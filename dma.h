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

extern u32 dma_bus_val;

// Resets DMA registers and state
void init_dma();

// Performs a DMA transfer for the specified channel.
cpu_alert_type dma_transfer(unsigned dma_chan, int *cycles);

// Handles a DMA control register write (might trigger a DMA)
cpu_alert_type iowrite_dma_cnt(u32 dma_number, u32 value);

// Savestate handlers
bool memdma_check_savestate(const u8 *src);
bool memdma_read_savestate(const u8 *src);
unsigned memdma_write_savestate(u8 *dst);

#ifdef __cplusplus
}
#endif

