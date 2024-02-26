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

#ifndef GBA_REGS_H
#define GBA_REGS_H

// Access to timer registers
#define REG_TMXD(n)   (REG_TM0D   + (2 * (n)))
#define REG_TMXCNT(n) (REG_TM0CNT + (2 * (n)))

typedef enum {
  // Video/Display registers
  REG_DISPCNT  = 0x00,
  REG_DISPSTAT = 0x02,
  REG_VCOUNT   = 0x03,
  REG_BG0CNT   = 0x04,
  REG_BG1CNT   = 0x05,
  REG_BG2CNT   = 0x06,
  REG_BG3CNT   = 0x07,
  REG_BG0HOFS  = 0x08,
  REG_BG0VOFS  = 0x09,
  REG_BG1HOFS  = 0x0A,
  REG_BG1VOFS  = 0x0B,
  REG_BG2HOFS  = 0x0C,
  REG_BG2VOFS  = 0x0D,
  REG_BG3HOFS  = 0x0E,
  REG_BG3VOFS  = 0x0F,
  REG_BG2PA    = 0x10,
  REG_BG2PB    = 0x11,
  REG_BG2PC    = 0x12,
  REG_BG2PD    = 0x13,
  REG_BG2X_L   = 0x14,
  REG_BG2X_H   = 0x15,
  REG_BG2Y_L   = 0x16,
  REG_BG2Y_H   = 0x17,
  REG_BG3PA    = 0x18,
  REG_BG3PB    = 0x19,
  REG_BG3PC    = 0x1A,
  REG_BG3PD    = 0x1B,
  REG_BG3X_L   = 0x1C,
  REG_BG3X_H   = 0x1D,
  REG_BG3Y_L   = 0x1E,
  REG_BG3Y_H   = 0x1F,
  REG_WIN0H    = 0x20,
  REG_WIN1H    = 0x21,
  REG_WIN0V    = 0x22,
  REG_WIN1V    = 0x23,
  REG_WININ    = 0x24,
  REG_WINOUT   = 0x25,
  REG_MOSAIC   = 0x26,
  REG_BLDCNT   = 0x28,
  REG_BLDALPHA = 0x29,
  REG_BLDY     = 0x2A,
  // Sound control registers
  REG_SOUND1CNT_L   = 0x30,
  REG_SOUND1CNT_H   = 0x31,
  REG_SOUND1CNT_X   = 0x32,
  REG_SOUND2CNT_L   = 0x34,
  REG_SOUND2CNT_H   = 0x36,
  REG_SOUND3CNT_L   = 0x38,
  REG_SOUND3CNT_H   = 0x39,
  REG_SOUND3CNT_X   = 0x3A,
  REG_SOUND4CNT_L   = 0x3C,
  REG_SOUND4CNT_H   = 0x3E,
  REG_SOUNDCNT_L    = 0x40,
  REG_SOUNDCNT_H    = 0x41,
  REG_SOUNDCNT_X    = 0x42,
  REG_SOUNDWAVE_0   = 0x48,
  REG_SOUNDWAVE_1   = 0x49,
  REG_SOUNDWAVE_2   = 0x4A,
  REG_SOUNDWAVE_3   = 0x4B,
  REG_SOUNDWAVE_4   = 0x4C,
  REG_SOUNDWAVE_5   = 0x4D,
  REG_SOUNDWAVE_6   = 0x4E,
  REG_SOUNDWAVE_7   = 0x4F,
  REG_SOUND_FIFOA_L = 0x50,
  REG_SOUND_FIFOA_H = 0x51,
  REG_SOUND_FIFOB_L = 0x52,
  REG_SOUND_FIFOB_H = 0x53,
  // DMA control
  REG_DMA0SAD   = 0x58,
  REG_DMA0DAD   = 0x5A,
  REG_DMA0CNT_L = 0x5C,
  REG_DMA0CNT_H = 0x5D,
  REG_DMA1SAD   = 0x5E,
  REG_DMA1DAD   = 0x60,
  REG_DMA1CNT_L = 0x62,
  REG_DMA1CNT_H = 0x63,
  REG_DMA2SAD   = 0x64,
  REG_DMA2DAD   = 0x66,
  REG_DMA2CNT_L = 0x68,
  REG_DMA2CNT_H = 0x69,
  REG_DMA3SAD   = 0x6A,
  REG_DMA3DAD   = 0x6C,
  REG_DMA3CNT_L = 0x6E,
  REG_DMA3CNT_H = 0x6F,
  // Timers
  REG_TM0D   = 0x80,
  REG_TM0CNT = 0x81,
  REG_TM1D   = 0x82,
  REG_TM1CNT = 0x83,
  REG_TM2D   = 0x84,
  REG_TM2CNT = 0x85,
  REG_TM3D   = 0x86,
  REG_TM3CNT = 0x87,
  // Serial
  REG_SIODATA32_L = 0x90,
  REG_SIODATA32_H = 0x91,
  REG_SIOMULTI0   = 0x90,
  REG_SIOMULTI1   = 0x91,
  REG_SIOMULTI2   = 0x92,
  REG_SIOMULTI3   = 0x93,
  REG_SIOCNT      = 0x94,
  REG_SIOMLT_SEND = 0x95,
  REG_SIODATA8    = 0x96,
  // Key input
  REG_P1    = 0x098,
  REG_P1CNT = 0x099,
  // More serial
  REG_RCNT = 0x9A,
  // Interrupt, waitstate, power.
  REG_IE      = 0x100,
  REG_IF      = 0x101,
  REG_WAITCNT = 0x102,
  REG_IME     = 0x104,
  REG_HALTCNT = 0x180
} hardware_register;

// Some useful macros to avoid reg math
#define REG_BGxCNT(n)  (REG_BG0CNT + (n))
#define REG_WINxH(n)   (REG_WIN0H  + (n))
#define REG_WINxV(n)   (REG_WIN0V  + (n))
#define REG_BGxHOFS(n) (REG_BG0HOFS + ((n) * 2))
#define REG_BGxVOFS(n) (REG_BG0VOFS + ((n) * 2))
#define REG_BGxPA(n)   (REG_BG2PA + ((n)-2)*8)
#define REG_BGxPB(n)   (REG_BG2PB + ((n)-2)*8)
#define REG_BGxPC(n)   (REG_BG2PC + ((n)-2)*8)
#define REG_BGxPD(n)   (REG_BG2PD + ((n)-2)*8)

#endif

