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
  // Immediate used for shift/rotate operations, as well as load/store
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
  u32 ro() const {
    return (opcode >> 6) & 0x7;
  }
  u32 rb() const {
    return (opcode >> 3) & 0x7;
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


class ARMInst {
public:
  u32 opcode;

  ARMInst(u32 opcode)
   : opcode(opcode) {}

  u32 cond() const {
    return (opcode >> 28) & 0xF;
  }
  u32 op8() const {
    return (opcode >> 20) & 0xFF;
  }

  // Immediates
  u32 imm8() const {
    return opcode & 0xFF;
  }
  u32 rot4() const {
    return (opcode >> 8) & 0xF;
  }
  u32 rot_imm8() const {
    u32 sa = rot4() * 2;
    return rotr32(imm8(), sa);
  }

  // Usual register info
  u32 rn() const {
    return (opcode >> 16) & 0xF;
  }
  u32 rd() const {
    return (opcode >> 12) & 0xF;
  }
  u32 rs() const {
    return (opcode >> 8) & 0xF;
  }
  u32 rm() const {
    return opcode & 0xF;
  }
  u32 rdhi() const {
    return (opcode >> 16) & 0xF;
  }
  u32 rdlo() const {
    return (opcode >> 12) & 0xF;
  }

  // Operand 2 bits and modes
  bool op2imm() const {
    // whether the register is shifted/rotated by an immediate or another reg.
    return (opcode & 0x10) == 0;
  }
  u32 op2smode() const {
    // Shift mode by the register op2 (lsl/lsr/asr/ror).
    return (opcode >> 5) & 0x3;
  }
  u32 op2sa() const {
    // Immediate amount of shift for op2
    return (opcode >> 7) & 0x1F;
  }

  // Branch
  s32 br_offset() const {
    // Returns already scaled (x4) offset for the branch.
    s32 r = opcode << 8;
    return r >> 6;
  }

  // MSR / MRS
  u32 psr_field() const {
    // Returns bits for flags and control only (no extension nor status)
    return ((opcode >> 16) & 1) | ((opcode >> 18) & 2);
  }

  // Memory instructions
  u16 rlist() const {
    return opcode & 0xFFFF;   // Reg list for STM/LDM
  }
  u32 off12() const {
    return opcode & 0xFFF;
  }
  u32 off8() const {
    return ((opcode >> 4) & 0xF0) | (opcode & 0x0F);
  }
};

