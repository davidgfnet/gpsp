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
}
#include "gba_memory_cpp.h"

u32 dma_bus_val;

template <u32 regnum>
inline u16 read_dmareg16(u32 dmachan) {
  u16 value = io_registers[regnum + dmachan * 6];
  return memswap(value);
}
template <u32 regnum>
inline u32 read_dmareg32(u32 dmachan) {
  u16 lo = io_registers[regnum + dmachan * 6];
  u16 hi = io_registers[regnum + dmachan * 6 + 1];
  u32 ret = lo | (hi << 16);
  return memswap(ret);
}
template <u32 regnum>
inline void write_dmareg16(u32 dmachan, u16 value) {
  io_registers[regnum + dmachan * 6] = memswap(value);
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

dma_transfer_type dma[4];

// The following map determines the region of each (assumes DMA access
// is not done out of bounds)

typedef enum {
  DMA_REGION_IWRAM        = 0,   // From/To IWRAM buffer (+SMC area)
  DMA_REGION_EWRAM        = 1,   // From/To EWRAM buffer (+SMC area)
  DMA_REGION_VRAM         = 2,   // From/To VRAM
  DMA_REGION_PALETTE_RAM  = 3,   // Writes require color conversion
  DMA_REGION_OAM_RAM      = 4,   // Writes require flagging
  DMA_REGION_IO           = 5,   // Writes go via memory handlers
  DMA_REGION_EXT          = 6,   // Writes go via memory handlers too
  DMA_REGION_GAMEPAK      = 7,   // Only reads, via memory buffers
  DMA_REGION_BUS          = 8,   // Reads open bus, no writes
  DMA_REGION_COUNT        = 9
} dma_region_type;

const dma_region_type dma_region_map[17] = {
  DMA_REGION_BUS,           // 0x00 - BUS
  DMA_REGION_BUS,           // 0x01 - BUS
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
  DMA_REGION_BUS            // 0x10 - Out of region (assuming open bus)
};


typedef u32 (*dma_reader_function)(u32 address);
typedef cpu_alert_type (*dma_writer_function)(u32 address, u32 value);


// Read functions for each memory area
template<typename tfsize>
u32 dmaread_iwram(u32 address) {
  return read_mem<tfsize>(&iwram[0x8000], address & 0x7FFF);
}
template<typename tfsize>
u32 dmaread_ewram(u32 address) {
  return read_mem<tfsize>(ewram, address & 0x3FFFF);
}
template<typename tfsize>
u32 dmaread_vram(u32 address) {
  u32 faddress = (address & 0x1FFFF);
  if (faddress >= 0x18000)
    faddress -= 0x8000;
  return read_mem<tfsize>((u8*)vram, faddress);
}
template<typename tfsize>
u32 dmaread_oamram(u32 address) {
  return read_mem<tfsize>((u8*)oam_ram, address & 0x3FF);
}
template<typename tfsize>
u32 dmaread_palram(u32 address) {
  return read_mem<tfsize>((u8*)palette_ram, address & 0x3FF);
}
template<typename tfsize>
u32 dmaread_ioregs(u32 address) {
  return read_mem<tfsize>((u8*)io_registers, address & 0x3FF);
}
template<typename tfsize>
u32 dmaread_ext(u32 address) {
  return read_memcb<tfsize>(address);
}
template<typename tfsize>
u32 dmaread_openbus(u32 address) {
  return (tfsize)dma_bus_val;
}
template<typename tfsize>
u32 dmaread_gamepak(u32 address) {
  u32 segment = address >> 15;
  const u8 *map = memory_map_read[segment];
  if (!map)
    map = load_gamepak_page(segment & 0x3FF);
  return read_mem<tfsize>(map, address & 0x7FFF);
}


// Write functions for each memory area
template<typename tfsize>
cpu_alert_type dmawrite_iwram(u32 address, u32 data) {
  address &= 0x7FFF;
  write_mem<tfsize>(&iwram[0x8000], address, (tfsize)data);
  return (*(tfsize*)(&iwram[address]) != 0) ? CPU_ALERT_SMC : CPU_ALERT_NONE;
}
template<typename tfsize>
cpu_alert_type dmawrite_ewram(u32 address, u32 data) {
  address &= 0x3FFFF;
  write_mem<tfsize>(ewram, address, (tfsize)data);
  return (*(tfsize*)(&ewram[address + 0x40000]) != 0) ? CPU_ALERT_SMC : CPU_ALERT_NONE;
}
template<typename tfsize>
cpu_alert_type dmawrite_vram(u32 address, u32 data) {
  u32 faddress = (address & 0x1FFFF);
  if (faddress >= 0x18000)
    faddress -= 0x8000;
  write_mem<tfsize>(vram, faddress, (tfsize)data);
  return CPU_ALERT_NONE;
}
template<typename tfsize>
cpu_alert_type dmawrite_oamram(u32 address, u32 data) {
  write_mem<tfsize>((u8*)oam_ram, address & 0x3FF, (tfsize)data);
  return CPU_ALERT_NONE;
}
template<typename tfsize>
cpu_alert_type dmawrite_palram(u32 address, u32 data) {
  write_palette<tfsize>(address & 0x3FF, (tfsize)data);
  return CPU_ALERT_NONE;
}
template<typename tfsize>
cpu_alert_type dmawrite_ioreg(u32 address, u32 data) {
  return write_ioregcb<tfsize>(address & 0x3FF, (tfsize)data);
}
template<typename tfsize>
cpu_alert_type dmawrite_ext(u32 address, u32 data) {
  return write_memcb<tfsize>(address, (tfsize)data);
}


// Describes a DMA transfer transaction.
class DMATransfer {
public:
  DMATransfer(u32 src, s32 src_strd, u32 dst, s32 dst_strd, u32 length)
   : src(src), dst(dst), src_strd(src_strd), dst_strd(dst_strd), length(length)
  {}

  u32 src, dst;
  s32 src_strd, dst_strd;
  u32 length;
};

// Given a read and write function, loops and proceed to copy data between spaces.
template <typename tfsize, dma_reader_function rdfn, dma_writer_function wrfn>
cpu_alert_type dma_tfsrcdst_loop(const DMATransfer &tf) {
  cpu_alert_type ret = CPU_ALERT_NONE;
  u32 srcptr = tf.src;
  u32 dstptr = tf.dst;
  tfsize tmp = 0;
  for (u32 i = 0; i < tf.length; i++) {
    tmp = (tfsize)rdfn(srcptr);
    ret |= wrfn(dstptr, tmp);
    srcptr += tf.src_strd;
    dstptr += tf.dst_strd;
  }
  // Update the DMA bus value for the next operation
  dma_bus_val = tmp;
  return ret;
}

template <typename tfsize, dma_reader_function rdfn>
cpu_alert_type dma_tfsrc_loop(const DMATransfer &tf) {
  u32 dst_region = MIN(tf.dst >> 24, 16);
  dma_region_type dst_region_type = dma_region_map[dst_region];

  switch (dst_region_type) {
  case DMA_REGION_IWRAM:
    return dma_tfsrcdst_loop<tfsize, rdfn, dmawrite_iwram<tfsize>>(tf);
  case DMA_REGION_EWRAM:
    return dma_tfsrcdst_loop<tfsize, rdfn, dmawrite_ewram<tfsize>>(tf);
  case DMA_REGION_VRAM:
    return dma_tfsrcdst_loop<tfsize, rdfn, dmawrite_vram<tfsize>>(tf);
  case DMA_REGION_PALETTE_RAM:
    return dma_tfsrcdst_loop<tfsize, rdfn, dmawrite_palram<tfsize>>(tf);
  case DMA_REGION_OAM_RAM:
    reg[OAM_UPDATED] = 1;     // Mark the OAM RAM as updated.
    return dma_tfsrcdst_loop<tfsize, rdfn, dmawrite_oamram<tfsize>>(tf);
  case DMA_REGION_IO:
    return dma_tfsrcdst_loop<tfsize, rdfn, dmawrite_ioreg<tfsize>>(tf);
  case DMA_REGION_EXT:
    return dma_tfsrcdst_loop<tfsize, rdfn, dmawrite_ext<tfsize>>(tf);
  case DMA_REGION_GAMEPAK:
  case DMA_REGION_BUS:
  default:
    // Improvement: this causes no read side-effects, like DMA bus value update
    return CPU_ALERT_NONE;    // Writes are ignored in these areas.
  };
}


template <typename tfsize>
cpu_alert_type dma_tf_loop(const DMATransfer &tf) {
  u32 src_region = MIN(tf.src >> 24, 16);
  dma_region_type src_region_type = dma_region_map[src_region];

  switch (src_region_type) {
  case DMA_REGION_IWRAM:
    return dma_tfsrc_loop<tfsize, dmaread_iwram<tfsize>>(tf);
  case DMA_REGION_EWRAM:
    return dma_tfsrc_loop<tfsize, dmaread_ewram<tfsize>>(tf);
  case DMA_REGION_VRAM:
    return dma_tfsrc_loop<tfsize, dmaread_vram<tfsize>>(tf);
  case DMA_REGION_PALETTE_RAM:
    return dma_tfsrc_loop<tfsize, dmaread_palram<tfsize>>(tf);
  case DMA_REGION_OAM_RAM:
    return dma_tfsrc_loop<tfsize, dmaread_oamram<tfsize>>(tf);
  case DMA_REGION_IO:
    return dma_tfsrc_loop<tfsize, dmaread_ioregs<tfsize>>(tf);
  case DMA_REGION_EXT:
    return dma_tfsrc_loop<tfsize, dmaread_ext<tfsize>>(tf);
  case DMA_REGION_GAMEPAK:
    return dma_tfsrc_loop<tfsize, dmaread_gamepak<tfsize>>(tf);
  case DMA_REGION_BUS:
  default:
    return dma_tfsrc_loop<tfsize, dmaread_openbus<tfsize>>(tf);
  };
}

static const int dma_stride[4] = {1, -1, 0, 1};

static cpu_alert_type dma_transfer_copy(
  dma_transfer_type *dmach, u32 src_ptr, u32 dest_ptr, u32 length)
{
  if (dmach->source_direction < 3) {
    int dst_stride = dma_stride[dmach->dest_direction];
    int src_stride = dma_stride[dmach->source_direction];
    bool dst_wb = dmach->dest_direction < 3;
    u32 stdsz = dmach->length_type == DMA_16BIT ? 2 : 4;

    DMATransfer tf(src_ptr, stdsz * src_stride, dest_ptr, stdsz * dst_stride, length);

    cpu_alert_type alert = (dmach->length_type == DMA_16BIT) ? dma_tf_loop<u16>(tf) :
                                                               dma_tf_loop<u32>(tf);

    // Update src/dest pointers. Is this necessary? They never get updated in the I/O space.
    dmach->source_address = src_ptr + stdsz * src_stride * length;
    if (dst_wb)   /* Update destination pointer if requested */
      dmach->dest_address = dest_ptr + stdsz * dst_stride * length;
                     
    return alert;
  }

  return CPU_ALERT_NONE;
}

cpu_alert_type dma_transfer(unsigned dma_chan, int *usedcycles)
{
  dma_transfer_type *dmach = &dma[dma_chan];
  u32 src_ptr = 0x0FFFFFFF & dmach->source_address & (
                   dmach->length_type == DMA_16BIT ? ~1U : ~3U);
  u32 dst_ptr = 0x0FFFFFFF & dmach->dest_address & (
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
    ret  = dma_transfer_copy(dmach, src_ptr, dst_ptr, blen0 >> tfsizes);
    ret |= dma_transfer_copy(dmach, src1, dst1, (byte_length - blen0) >> tfsizes);
  }
  else if (dst_reg0 == dst_reg1) {
    // Dest stays within the region, source crosses over
    u32 blen0 = dma_stride[dmach->source_direction] < 0 ?
        src_ptr & 0xFFFFFF : 0x1000000 - (src_ptr & 0xFFFFFF);
    u32 src1 = src_ptr + blen0 * dma_stride[dmach->source_direction];
    u32 dst1 = dst_ptr + blen0 * dma_stride[dmach->dest_direction];
    ret  = dma_transfer_copy(dmach, src_ptr, dst_ptr, blen0 >> tfsizes);
    ret |= dma_transfer_copy(dmach, src1, dst1, (byte_length - blen0) >> tfsizes);
  }
  // TODO: We do not cover the three-region case, seems no game uses that?
  // Lucky Luke does cross dest region due to some off-by-one error.

  if((dmach->repeat_type == DMA_NO_REPEAT) ||
   (dmach->start_type == DMA_START_IMMEDIATELY))
  {
    u16 cntrl = read_dmareg16<REG_DMA0CNT_H>(dma_chan);
    write_dmareg16<REG_DMA0CNT_H>(dma_chan, cntrl & (~0x8000));
    dmach->start_type = DMA_INACTIVE;
  }

  // Trigger an IRQ if configured to do so.
  if (dmach->irq)
    ret |= flag_interrupt(IRQ_DMA0 << dma_chan);

  // This is an approximation for the most common case (no region cross)
  if (usedcycles)
    *usedcycles += dmach->length * (
       def_seq_cycles[src_ptr >> 24][tfsizes - 1] +
       def_seq_cycles[dst_ptr >> 24][tfsizes - 1]);

  return ret;
}

cpu_alert_type iowrite_dma_cnt(u32 dma_number, u32 value) {
  if(value & 0x8000) {
    if(dma[dma_number].start_type == DMA_INACTIVE) {
      u32 start_type = ((value >> 12) & 0x03);
      u32 src_address = 0xFFFFFFF & read_dmareg32<REG_DMA0SAD>(dma_number);
      u32 dst_address = 0xFFFFFFF & read_dmareg32<REG_DMA0DAD>(dma_number);

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
      else {
        u32 length = read_dmareg16<REG_DMA0CNT_L>(dma_number);

        // Autodetecting EEPROM size (a bit of a hack!)
        if((dma_number == 3) && ((dst_address >> 24) == 0x0D) &&
         ((length & 0x1F) == 17))
          eeprom_size = EEPROM_8_KBYTE;

        if(dma_number < 3)
          length &= 0x3FFF;

        if(length == 0) {
          if(dma_number == 3)
            length = 0x10000;
          else
            length = 0x04000;
        }

        dma[dma_number].length = length;
        dma[dma_number].length_type = ((value >> 10) & 0x01);
        dma[dma_number].dest_direction = ((value >> 5) & 3);
      }

      write_dmareg16<REG_DMA0CNT_H>(dma_number, value);

      if(start_type == DMA_START_IMMEDIATELY) {
        // Excutes the DMA now! Copies the data and returns side effects.
        int dma_cycles = 0;
        cpu_alert_type ret = dma_transfer(dma_number, &dma_cycles);
        if (!dma_cycles)
          return ret;
        // Sleep CPU for N cycles and return HALT as side effect (so it does).
        reg[CPU_HALT_STATE] = CPU_DMA;
        reg[REG_SLEEP_CYCLES] = 0x80000000 | (u32)dma_cycles;
        return CPU_ALERT_HALT | ret;
      }
    }
  } else {
    // Disables DMA
    dma[dma_number].start_type = DMA_INACTIVE;
    dma[dma_number].direct_sound_channel = DMA_NO_DIRECT_SOUND;
    write_dmareg16<REG_DMA0CNT_H>(dma_number, value);
  }

  return CPU_ALERT_NONE;
}

void init_dma() {
  for (int i = 0; i < DMA_CHAN_CNT; i++) {
    dma[i].start_type = DMA_INACTIVE;
    dma[i].irq = DMA_NO_IRQ;
    dma[i].source_address = dma[i].dest_address = 0;
    dma[i].source_direction = dma[i].dest_direction = 0;
    dma[i].length = 0;
    dma[i].length_type = DMA_16BIT;
    dma[i].repeat_type = DMA_NO_REPEAT;
    dma[i].direct_sound_channel = DMA_NO_DIRECT_SOUND;
  }
  // Using zero value as DMA bus initial value (likely not accurate)
  dma_bus_val = 0;
}

bool memdma_check_savestate(const u8 *src) {
  const u8 *dmadoc = bson_find_key(src, "dma");
  if (!dmadoc)
    return false;

  static const char *dmavars32[] = {
    "src-addr", "dst-addr", "src-dir", "dst-dir",
    "len", "size", "repeat", "start", "dsc", "irq"
  };

  for (unsigned i = 0; i < DMA_CHAN_CNT; i++) {
    char tname[2] = {(char)('0' + i), 0};
    const u8 *dmastr = bson_find_key(dmadoc, tname);
    if (!dmastr)
      return false;

    for (i = 0; i < sizeof(dmavars32)/sizeof(dmavars32[0]); i++)
      if (!bson_contains_key(dmastr, dmavars32[i], BSON_TYPE_INT32))
        return false;
  }
  return true;
}

bool memdma_read_savestate(const u8 *src) {
  const u8 *dmadoc = bson_find_key(src, "dma");
  if (!dmadoc)
    return false;

  for (unsigned i = 0; i < DMA_CHAN_CNT; i++) {
    char tname[2] = {(char)('0' + i), 0};
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

unsigned memdma_write_savestate(u8 *dst) {
  u8 *wbptr, *startp = dst;

  bson_start_document(dst, "dma", wbptr);
  for (unsigned i = 0; i < DMA_CHAN_CNT; i++) {
    u8 *wbptr2;
    char tname[2] = {(char)('0' + i), 0};
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

