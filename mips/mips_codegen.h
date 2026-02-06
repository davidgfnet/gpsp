/* gameplaySP
 *
 * Copyright (C) 2006 Exophase <exophase@gmail.com>
 * Copyright (C) 2026 David Guillen Fandos <david@davidgf.net>
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

#ifndef __MIPS_CODEGEN__HH__
#define __MIPS_CODEGEN__HH__

typedef enum {
  mips_reg_zero =  0,
  mips_reg_at   =  1,
  mips_reg_v0   =  2,
  mips_reg_v1   =  3,
  mips_reg_a0   =  4,
  mips_reg_a1   =  5,
  mips_reg_a2   =  6,
  mips_reg_a3   =  7,
  mips_reg_t0   =  8,
  mips_reg_t1   =  9,
  mips_reg_t2   = 10,
  mips_reg_t3   = 11,
  mips_reg_t4   = 12,
  mips_reg_t5   = 13,
  mips_reg_t6   = 14,
  mips_reg_t7   = 15,
  mips_reg_s0   = 16,
  mips_reg_s1   = 17,
  mips_reg_s2   = 18,
  mips_reg_s3   = 19,
  mips_reg_s4   = 20,
  mips_reg_s5   = 21,
  mips_reg_s6   = 22,
  mips_reg_s7   = 23,
  mips_reg_t8   = 24,
  mips_reg_t9   = 25,
  mips_reg_k0   = 26,
  mips_reg_k1   = 27,
  mips_reg_gp   = 28,
  mips_reg_sp   = 29,
  mips_reg_fp   = 30,
  mips_reg_ra   = 31
} mips_regnum;

typedef enum {
  mips_special_sll       = 0x00,
  mips_special_srl       = 0x02,
  mips_special_sra       = 0x03,
  mips_special_sllv      = 0x04,
  mips_special_srlv      = 0x06,
  mips_special_srav      = 0x07,
  mips_special_jr        = 0x08,
  mips_special_jalr      = 0x09,
  mips_special_movz      = 0x0A,
  mips_special_movn      = 0x0B,
  mips_special_sync      = 0x0F,
  mips_special_mfhi      = 0x10,
  mips_special_mthi      = 0x11,
  mips_special_mflo      = 0x12,
  mips_special_mtlo      = 0x13,
  mips_special_mult      = 0x18,
  mips_special_multu     = 0x19,
  mips_special_div       = 0x1A,
  mips_special_divu      = 0x1B,
  mips_special_madd      = 0x1C,
  mips_special_maddu     = 0x1D,
  mips_special_add       = 0x20,
  mips_special_addu      = 0x21,
  mips_special_sub       = 0x22,
  mips_special_subu      = 0x23,
  mips_special_and       = 0x24,
  mips_special_or        = 0x25,
  mips_special_xor       = 0x26,
  mips_special_nor       = 0x27,
  mips_special_slt       = 0x2A,
  mips_special_sltu      = 0x2B,
  mips_special_max       = 0x2C,
  mips_special_min       = 0x2D,
} mips_function_special;

typedef enum
{
  mips_special2_madd     = 0x00,
  mips_special2_maddu    = 0x01,
} mips_function_special2;

typedef enum
{
  mips_special3_ext      = 0x00,
  mips_special3_ins      = 0x04,
  mips_special3_bshfl    = 0x20
} mips_function_special3;

typedef enum
{
  mips_bshfl_seb      = 0x10,
  mips_bshfl_seh      = 0x18,
  mips_bshfl_wsbh     = 0x02,
} mips_function_bshfl;

typedef enum
{
  mips_regimm_bltz       = 0x00,
  mips_regimm_bltzal     = 0x10,
  mips_regimm_bgezal     = 0x11,
  mips_regimm_synci      = 0x1F
} mips_function_regimm;

typedef enum
{
  mips_opcode_special    = 0x00,
  mips_opcode_regimm     = 0x01,
  mips_opcode_j          = 0x02,
  mips_opcode_jal        = 0x03,
  mips_opcode_beq        = 0x04,
  mips_opcode_bne        = 0x05,
  mips_opcode_blez       = 0x06,
  mips_opcode_bgtz       = 0x07,
  mips_opcode_addi       = 0x08,
  mips_opcode_addiu      = 0x09,
  mips_opcode_slti       = 0x0A,
  mips_opcode_sltiu      = 0x0B,
  mips_opcode_andi       = 0x0C,
  mips_opcode_ori        = 0x0D,
  mips_opcode_xori       = 0x0E,
  mips_opcode_lui        = 0x0F,
  mips_opcode_llo        = 0x18,
  mips_opcode_lhi        = 0x19,
  mips_opcode_trap       = 0x1A,
  mips_opcode_special2   = 0x1C,
  mips_opcode_special3   = 0x1F,
  mips_opcode_lb         = 0x20,
  mips_opcode_lh         = 0x21,
  mips_opcode_lw         = 0x23,
  mips_opcode_lbu        = 0x24,
  mips_opcode_lhu        = 0x25,
  mips_opcode_sb         = 0x28,
  mips_opcode_sh         = 0x29,
  mips_opcode_sw         = 0x2B,
  mips_opcode_cache      = 0x2F,
} mips_opcode;

class MIPSEmitter : public CodeEmitterBase {
private:

  inline void emit_inst(uint32_t opcode, uint32_t args) {
    *(uint32_t*)this->emit_ptr = (opcode << 26) | args;
    this->emit_ptr += 4;
  }

  inline void emit_imm(uint32_t opcode, uint32_t rs, uint32_t rt, uint16_t imm) {
    emit_inst(opcode, (rs << 21) | (rt << 16) | imm);
  }

  inline void emit_special(mips_function_special fn, uint32_t rs, uint32_t rt, uint32_t rd, uint8_t shift) {
    emit_inst(mips_opcode_special, (rs << 21) | (rt << 16) | (rd << 11) | (shift << 6) | fn);
  }

  inline void emit_special2(mips_function_special2 fn, uint32_t rs, uint32_t rt, uint32_t rd, uint8_t shift) {
    emit_inst(mips_opcode_special2, (rs << 21) | (rt << 16) | (rd << 11) | (shift << 6) | fn);
  }

  inline void emit_special3(mips_function_special3 fn, uint32_t rs, uint32_t rt, uint32_t imma, uint32_t immb) {
    emit_inst(mips_opcode_special3, (rs << 21) | (rt << 16) | (imma << 11) | (immb << 6) | fn);
  }


public:

  MIPSEmitter(uint8_t *emit_ptr)
   : CodeEmitterBase(emit_ptr) {}

  inline void emit_nop() {
    emit_sll(mips_reg_zero, mips_reg_zero, 0);
  }
  inline void emit_sync() {
    emit_special(mips_special_sync, 0, 0, 0, 0);
  }

  inline void emit_lui(mips_regnum rt, uint16_t imm) {
    emit_imm(mips_opcode_lui, 0, rt, imm);
  }

  // Immediate instructions (16 bit imm)
  inline void emit_addiu(mips_regnum rt, mips_regnum rs, uint16_t imm) {
    emit_imm(mips_opcode_addiu, rs, rt, imm);
  }
  inline void emit_xori(mips_regnum rt, mips_regnum rs, uint16_t imm) {
    emit_imm(mips_opcode_xori, rs, rt, imm);
  }
  inline void emit_andi(mips_regnum rt, mips_regnum rs, uint16_t imm) {
    emit_imm(mips_opcode_andi, rs, rt, imm);
  }
  inline void emit_ori(mips_regnum rt, mips_regnum rs, uint16_t imm) {
    emit_imm(mips_opcode_ori, rs, rt, imm);
  }
  inline void emit_slti(mips_regnum rt, mips_regnum rs, uint16_t imm) {
    emit_imm(mips_opcode_slti, rs, rt, imm);
  }
  inline void emit_sltiu(mips_regnum rt, mips_regnum rs, uint16_t imm) {
    emit_imm(mips_opcode_sltiu, rs, rt, imm);
  }

  // Memory (load/store) opcodes
  inline void emit_lw(mips_regnum rt, mips_regnum rs, uint16_t imm) {
    emit_imm(mips_opcode_lw, rs, rt, imm);
  }
  inline void emit_sw(mips_regnum rt, mips_regnum rs, uint16_t imm) {
    emit_imm(mips_opcode_sw, rs, rt, imm);
  }
  inline void emit_lb(mips_regnum rt, mips_regnum rs, uint16_t imm) {
    emit_imm(mips_opcode_lb, rs, rt, imm);
  }
  inline void emit_lbu(mips_regnum rt, mips_regnum rs, uint16_t imm) {
    emit_imm(mips_opcode_lbu, rs, rt, imm);
  }
  inline void emit_sb(mips_regnum rt, mips_regnum rs, uint16_t imm) {
    emit_imm(mips_opcode_sb, rs, rt, imm);
  }
  inline void emit_lh(mips_regnum rt, mips_regnum rs, uint16_t imm) {
    emit_imm(mips_opcode_lh, rs, rt, imm);
  }
  inline void emit_lhu(mips_regnum rt, mips_regnum rs, uint16_t imm) {
    emit_imm(mips_opcode_lhu, rs, rt, imm);
  }
  inline void emit_sh(mips_regnum rt, mips_regnum rs, uint16_t imm) {
    emit_imm(mips_opcode_sh, rs, rt, imm);
  }

  // Shift special opcodes
  inline void emit_sll(mips_regnum rd, mips_regnum rt, uint8_t shift) {
    emit_special(mips_special_sll, 0, rt, rd, shift);
  }
  inline void emit_srl(mips_regnum rd, mips_regnum rt, uint8_t shift) {
    emit_special(mips_special_srl, 0, rt, rd, shift);
  }
  inline void emit_sra(mips_regnum rd, mips_regnum rt, uint8_t shift) {
    emit_special(mips_special_sra, 0, rt, rd, shift);
  }
  inline void emit_rotr(mips_regnum rd, mips_regnum rt, uint8_t shift) {
    emit_special(mips_special_srl, 1, rt, rd, shift);
  }
  inline void emit_sllv(mips_regnum rd, mips_regnum rt, mips_regnum rs) {
    emit_special(mips_special_sllv, rs, rt, rd, 0);
  }
  inline void emit_srlv(mips_regnum rd, mips_regnum rt, mips_regnum rs) {
    emit_special(mips_special_srlv, rs, rt, rd, 0);
  }
  inline void emit_srav(mips_regnum rd, mips_regnum rt, mips_regnum rs) {
    emit_special(mips_special_srav, rs, rt, rd, 0);
  }
  inline void emit_rotrv(mips_regnum rd, mips_regnum rt, mips_regnum rs) {
    emit_special(mips_special_srlv, rs, rt, rd, 1);
  }

  // Arithmetic instructions (reg)
  inline void emit_addu(mips_regnum rd, mips_regnum rs, mips_regnum rt) {
    emit_special(mips_special_addu, rs, rt, rd, 0);
  }
  inline void emit_subu(mips_regnum rd, mips_regnum rs, mips_regnum rt) {
    emit_special(mips_special_subu, rs, rt, rd, 0);
  }
  inline void emit_slt(mips_regnum rd, mips_regnum rs, mips_regnum rt) {
    emit_special(mips_special_slt, rs, rt, rd, 0);
  }
  inline void emit_sltu(mips_regnum rd, mips_regnum rs, mips_regnum rt) {
    emit_special(mips_special_sltu, rs, rt, rd, 0);
  }
  inline void emit_max(mips_regnum rd, mips_regnum rs, mips_regnum rt) {
    emit_special(mips_special_max, rs, rt, rd, 0);
  }
  inline void emit_min(mips_regnum rd, mips_regnum rs, mips_regnum rt) {
    emit_special(mips_special_min, rs, rt, rd, 0);
  }

  // Logic instructions (reg)
  inline void emit_xor(mips_regnum rd, mips_regnum rs, mips_regnum rt) {
    emit_special(mips_special_xor, rs, rt, rd, 0);
  }
  inline void emit_and(mips_regnum rd, mips_regnum rs, mips_regnum rt) {
    emit_special(mips_special_and, rs, rt, rd, 0);
  }
  inline void emit_or(mips_regnum rd, mips_regnum rs, mips_regnum rt) {
    emit_special(mips_special_or, rs, rt, rd, 0);
  }
  inline void emit_nor(mips_regnum rd, mips_regnum rs, mips_regnum rt) {
    emit_special(mips_special_nor, rs, rt, rd, 0);
  }
  inline void emit_movn(mips_regnum rd, mips_regnum rs, mips_regnum rt) {
    emit_special(mips_special_movn, rs, rt, rd, 0);
  }
  inline void emit_movz(mips_regnum rd, mips_regnum rs, mips_regnum rt) {
    emit_special(mips_special_movz, rs, rt, rd, 0);
  }

  inline void emit_ext(mips_regnum rt, mips_regnum rs, uint8_t pos, uint8_t size) {
    emit_special3(mips_special3_ext, rs, rt, (size - 1), pos);
  }
  inline void emit_ins(mips_regnum rt, mips_regnum rs, uint8_t pos, uint8_t size) {
    emit_special3(mips_special3_ins, rs, rt, (pos + size - 1), pos);
  }
  inline void emit_seb(mips_regnum rd, mips_regnum rt) {
    emit_special3(mips_special3_bshfl, 0, rt, rd, mips_bshfl_seb);
  }
  inline void emit_seh(mips_regnum rd, mips_regnum rt) {
    emit_special3(mips_special3_bshfl, 0, rt, rd, mips_bshfl_seh);
  }

  // mul/div
  inline void emit_mfhi(mips_regnum rd) {
    emit_special(mips_special_mfhi, 0, 0, rd, 0);
  }
  inline void emit_mflo(mips_regnum rd) {
    emit_special(mips_special_mflo, 0, 0, rd, 0);
  }
  inline void emit_mthi(mips_regnum rs) {
    emit_special(mips_special_mthi, rs, 0, 0, 0);
  }
  inline void emit_mtlo(mips_regnum rs) {
    emit_special(mips_special_mtlo, rs, 0, 0, 0);
  }
  inline void emit_mult(mips_regnum rs, mips_regnum rt) {
    emit_special(mips_special_mult, rs, rt, 0, 0);
  }
  inline void emit_multu(mips_regnum rs, mips_regnum rt) {
    emit_special(mips_special_multu, rs, rt, 0, 0);
  }
  inline void emit_div(mips_regnum rs, mips_regnum rt) {
    emit_special(mips_special_div, rs, rt, 0, 0);
  }
  inline void emit_divu(mips_regnum rs, mips_regnum rt) {
    emit_special(mips_special_divu, rs, rt, 0, 0);
  }

  inline void emit_madd(mips_regnum rs, mips_regnum rt) {
    #ifdef PSP
      emit_special(mips_special_madd, rs, rt, 0, 0);
    #else
      emit_special2(mips_special2_madd, rs, rt, 0, 0);
    #endif
  }
  inline void emit_maddu(mips_regnum rs, mips_regnum rt) {
    #ifdef PSP
      emit_special(mips_special_maddu, rs, rt, 0, 0);
    #else
      emit_special2(mips_special2_maddu, rs, rt, 0, 0);
    #endif
  }

  // Branching/calling
  inline uint8_t* emit_j(uint32_t offset) {
    u8 *ret = this->emit_ptr;
    emit_inst(mips_opcode_j, offset & 0x3FFFFFF);
    return ret;
  }
  inline void emit_jal(uint32_t offset) {
    emit_inst(mips_opcode_jal, offset & 0x3FFFFFF);
  }
  inline void emit_jr(mips_regnum rs) {
    emit_special(mips_special_jr, rs, 0, 0, 0);
  }
  inline void emit_jalr(mips_regnum rs) {
    emit_special(mips_special_jalr, rs, 0, 31, 0);
  }
  inline uint8_t* emit_bne(mips_regnum rs, mips_regnum rt, uint16_t imm) {
    u8 *ret = this->emit_ptr;
    emit_imm(mips_opcode_bne, rs, rt, imm);
    return ret;
  }
  inline uint8_t* emit_beq(mips_regnum rs, mips_regnum rt, uint16_t imm) {
    u8 *ret = this->emit_ptr;
    emit_imm(mips_opcode_beq, rs, rt, imm);
    return ret;
  }
  inline void emit_bltzal(mips_regnum rs, uint16_t imm) {
    emit_imm(mips_opcode_regimm, rs, mips_regimm_bltzal, imm);
  }
  inline void emit_bgezal(mips_regnum rs, uint16_t imm) {
    emit_imm(mips_opcode_regimm, rs, mips_regimm_bgezal, imm);
  }
  inline void emit_bltz(mips_regnum rs, uint16_t imm) {
    emit_imm(mips_opcode_regimm, rs, mips_regimm_bltz, imm);
  }

  // Misc
  inline void emit_cache(uint8_t operation, mips_regnum rs, uint16_t imm) {
    emit_inst(mips_opcode_cache, (rs << 21) | (operation << 16) | imm);
  }
  inline void emit_synci(mips_regnum rs, uint16_t imm) {
    emit_imm(mips_opcode_regimm, rs, mips_regimm_synci, imm);
  }

};

#define mips_relative_offset(source, offset)                                  \
  (((u32)offset - ((u32)source + 4)) / 4)                                     \

#define mips_absolute_offset(offset)                                          \
  ((u32)offset / 4)                                                           \

#endif

