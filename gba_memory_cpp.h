/* gameplaySP
 *
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

// This is a temporary file that will go away soon!

#ifndef MEMORY_H_CPP
#define MEMORY_H_CPP

// Byte swap/ordering routines
inline u8 memswap(u8 v) { return v; }
inline s8 memswap(s8 v) { return v; }
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
  inline u16 memswap(u16 v) { return __builtin_bswap16(v); }
  inline u32 memswap(u32 v) { return __builtin_bswap32(v); }
  inline u64 memswap(u64 v) { return __builtin_bswap64(v); }
#else
  inline u16 memswap(u16 v) { return v; }
  inline u32 memswap(u32 v) { return v; }
  inline u64 memswap(u64 v) { return v; }
#endif

// Reads memory from the buffer directly, performing any necessary byte swaps
// For little endian platforms this is just a single load.
// The signed case is always a bit special (for s16).
template <typename memtype>
inline memtype read_mem(const u8 *block, u32 offset) {
  const memtype *ptr = (memtype*)(&block[offset]);
  return memswap(*ptr);
}
template <>
inline s16 read_mem(const u8 *block, u32 offset) {
  const u16 *ptr = (u16*)(&block[offset]);
  return (s16)memswap(*ptr);
}

template <typename memtype>
inline void write_mem(u8 *block, u32 offset, memtype value) {
  memtype *ptr = (memtype*)(&block[offset]);
  *ptr = memswap(value);
}

// If necessary, memory can be read using the regular handlers, this is for
// special cases that need some handling like open bus.
template <typename memtype>
inline memtype read_memcb(u32 address);

template <>
inline u8 read_memcb(u32 address) {
  return read_memory8(address);
}
template <>
inline s8 read_memcb(u32 address) {
  return (s8)read_memory8(address);
}
template <>
inline u16 read_memcb(u32 address) {
  return read_memory16(address);
}
template <>
inline s16 read_memcb(u32 address) {
  return read_memory16_signed(address);
}
template <>
inline u32 read_memcb(u32 address) {
  return read_memory32(address);
}

// Similarly writes can also be written using a handler:

template <typename memtype>
inline cpu_alert_type write_memcb(u32 address, memtype data);

template <>
inline cpu_alert_type write_memcb(u32 address, u8 data) {
  return write_memory8(address, data);
}
template <>
inline cpu_alert_type write_memcb(u32 address, u16 data) {
  return write_memory16(address, data);
} 
template <>
inline cpu_alert_type write_memcb(u32 address, u32 data) {
  return write_memory32(address, data);
}


// Memory specific routines for I/O, palette...
template <typename memtype>
inline cpu_alert_type write_ioregcb(u32 address, memtype data);

template <>
inline cpu_alert_type write_ioregcb(u32 address, u8 data) {
  return write_io_register8(address, data);
}
template <>
inline cpu_alert_type write_ioregcb(u32 address, u16 data) {
  return write_io_register16(address, data);
}
template <>
inline cpu_alert_type write_ioregcb(u32 address, u32 data) {
  return write_io_register32(address, data);
}

template <typename memtype>
inline void write_palette(u32 address, memtype value);

template <>
inline void write_palette(u32 address, u16 value) {
  u16 cvalue = convert_palette(value);
  write_mem((u8*)palette_ram, address, value);
  write_mem((u8*)palette_ram_converted, address, cvalue);
}
template <>
inline void write_palette(u32 address, u8 value) {
  // the byte is duplicated and a full half-word is written (16 bit bus!)
  write_palette<u16>(address & ~1U, (value << 8) | value);
}
template <>
inline void write_palette(u32 address, u32 value) {
  write_palette<u16>(address,     (u16)(value & 0xFFFF));
  write_palette<u16>(address + 2, (u16)(value >> 16));
}


#endif

