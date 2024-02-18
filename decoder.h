/* gameplaySP
 *
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

// ARM and Thumb decoding code, for convenience and to unify all the decoding
// paths existing in the emulator.

class ThumbInst {
public:
  u16 opcode;

  ThumbInst(u16 opcode)
   : opcode(opcode) {}

  u32 imm8() const {
    return opcode & 0xFF;
  }
  s32 imm71() const {
    s32 i = opcode & 0x7F;
    return (opcode & 0x80) ? -i : i;
  }
    u32 imm = (opcode & 0x7F);
  // Immediate used for shift/rotate operations
  u32 imm5() const {
    return (opcode >> 6) & 0x1F;
  }
  // Used for small ALU operations
  u32 imm3() const {
    return (opcode >> 6) & 0x7;
  }

  // source register for most ALU operations
  u8 rs() const {
    return (opcode >> 3) & 0x07;
  }
  // destination register for most ALU operations
  u8 rd() const {
    return opcode & 0x7;
  }
  // used in some 3 operand instructions
  u8 rn() const {
    return (opcode >> 6) & 0x7;
  }
  // For instructions that deal with PC/SP
  u8 rd8() const {
    return (opcode >> 8) & 0x7;
  }

  // Memory instructions encodings
  u8 rlist() const {
    return opcode & 0xFF;         // Register list for push/pop/ldm/stm
  }
  u8 rptr() const {
    return (opcode >> 8) & 0x7;   // Base reg for ldm/stm
  }

  // Hireg resgister encodings
  u8 rs_hi() const {
    return (opcode >> 3) & 0xF;
  }
  u8 rd_hi() const {
    return ((opcode >> 4) & 0x08) | (opcode & 0x07);
  }

  // Branch offsets (already scaled)
  s32 cbr_offset() const {
    s32 offset = (s8)(opcode & 0xFF);
    return offset * 2;
  }
  s32 abr_offset() const {
    u32 uoff = (opcode & 0x07FF) << 21;
    s32 soff = (s32)uoff;
    return soff >> 20;
  }
  s32 abr_offset_hi() const {
    u32 uoff = (opcode & 0x07FF) << 21;
    s32 soff = (s32)uoff;
    return soff >> 9;
  }
  u32 abr_offset_lo() const {
    return (opcode & 0x07FF) << 1;
  }
};

