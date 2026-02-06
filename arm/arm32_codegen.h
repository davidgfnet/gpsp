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

#ifndef __ARM_CODEGEN_H_
#define __ARM_CODEGEN_H_

#include "basedefs.h"

typedef enum {
  armcg_reg0  =  0,
  armcg_reg1  =  1,
  armcg_reg2  =  2,
  armcg_reg3  =  3,
  armcg_reg4  =  4,
  armcg_reg5  =  5,
  armcg_reg6  =  6,
  armcg_reg7  =  7,
  armcg_reg8  =  8,
  armcg_reg9  =  9,
  armcg_reg10 = 10,
  armcg_reg11 = 11,
  armcg_reg12 = 12,
  armcg_reg13 = 13,
  armcg_reg14 = 14,
  armcg_reg15 = 15,

  armcg_regsp = 13,
  armcg_reglr = 14,
  armcg_regpc = 15,

  armcg_reginvalid = 16,
} armcg_regnum;

typedef enum {
  armgc_mul   = 0x0,
  armgc_mla   = 0x1,

  armgc_umull = 0x4,
  armgc_umlal = 0x5,
  armgc_smull = 0x6,
  armgc_smlal = 0x7,
} armcg_mulopc;

typedef enum {
  armgc_psr_c = 1,
  armgc_psr_x = 2,
  armgc_psr_s = 4,
  armgc_psr_f = 8,
} armcg_psrmask;

typedef ARMOp armcg_op;

class ARMEmitter : public CodeEmitterBase {
private:

  inline void emit_inst(uint32_t condc, uint32_t inst) {
    *(uint32_t*)this->emit_ptr = (condc << 28) | inst;
    this->emit_ptr += 4;
  }

  inline void emit_memop(uint32_t rd, uint32_t rn, uint32_t opcode, uint32_t imm) {
    emit_inst(0xE, (rd << 12) | (rn << 16) | (opcode << 20) | imm);
  }

  template <bool load, bool wrb, bool up, bool prei>
  inline void emit_ldmstm(armcg_regnum breg, uint16_t reglist) {
    emit_inst(0xE, reglist | (breg << 16) | 0x08000000 |
                   ((load ? 1 : 0) << 20) |
                   ((wrb  ? 1 : 0) << 21) |
                   ((up   ? 1 : 0) << 23) |
                   ((prei ? 1 : 0) << 24));
  }

  template <armcg_op op, FlagOperation flg>
  inline void emit_aluop_reg(uint32_t rd, uint32_t rn, uint32_t op2) {
    emit_inst(0xE, (flg == SetFlags ? (1<<20) : 0) | (rd << 12) | (rn << 16) | (op << 21) | op2);
  }

  template <armcg_op op, FlagOperation flg>
  inline void emit_aluop_imm(uint32_t rd, uint32_t rn, uint32_t op2) {
    emit_inst(0xE, (1<<25) | (flg == SetFlags ? (1<<20) : 0) | (rd << 12) | (rn << 16) | (op << 21) | op2);
  }

  // Register shifted by some register amount
  inline uint32_t op2regreg(uint32_t rm, uint32_t smode, uint32_t rs) {
    return rm | (1 << 4) | (smode << 5) | (rs << 8);
  }
  // Register shifted by some immediate amount
  inline uint32_t op2regimm(uint32_t rm, uint32_t smode, uint32_t samount) {
    return rm | (smode << 5) | (samount << 7);
  }
  // Immediate (rotated by 16 possible rotations).
  inline uint32_t op2imm(uint32_t imm, uint32_t amount) {
    return imm | (amount << 8);
  }

public:

  ARMEmitter(uint8_t *emit_ptr)
   : CodeEmitterBase(emit_ptr) {}

  // Performs an ALU operation (with/out flag setting) with some immediate shift amount
  template <armcg_op op, FlagOperation flg>
  inline void emit_alu_reg_immshift(armcg_regnum rd, armcg_regnum rn, armcg_regnum rm, uint32_t smode = ShiftLSL, uint32_t samount = 0) {
    emit_aluop_reg<op, flg>(rd, rn, op2regimm(rm, smode, samount));
  }

  // Performs an ALU operation (with/out flag setting) with some reg shift amount
  template <armcg_op op, FlagOperation flg>
  inline void emit_alu_reg_regshift(armcg_regnum rd, armcg_regnum rn, armcg_regnum rm, uint32_t smode, uint32_t rs) {
    emit_aluop_reg<op, flg>(rd, rn, op2regreg(rm, smode, rs));
  }

  // Performs an ALU operation (with/out flag setting) with some immediate value
  template <armcg_op op, FlagOperation flg>
  inline void emit_alu_imm(armcg_regnum rd, armcg_regnum rn, uint32_t imrot, uint8_t imm8) {
    emit_aluop_imm<op, flg>(rd, rn, op2imm(imm8, imrot));
  }

  // 2 Operands (testing), always generates flags.
  template <armcg_op op>
  inline void emit_test_reg_immshift(armcg_regnum rn, armcg_regnum rm, uint32_t smode = ShiftLSL, uint32_t samount = 0) {
    emit_aluop_reg<op, SetFlags>(0, rn, op2regimm(rm, smode, samount));
  }
  template <armcg_op op>
  inline void emit_test_reg_regshift(armcg_regnum rn, armcg_regnum rm, uint32_t smode, uint32_t rs) {
    emit_aluop_reg<op, SetFlags>(0, rn, op2regreg(rm, smode, rs));
  }
  template <armcg_op op>
  inline void emit_test_imm(armcg_regnum rn, uint32_t imrot, uint8_t imm8) {
    emit_aluop_imm<op, SetFlags>(0, rn, op2imm(imm8, imrot));
  }

  // Unary operations, ie. mov/mvn
  template <armcg_op op, FlagOperation flg>
  inline void emit_mov_reg_immshift(armcg_regnum rd, armcg_regnum rm, uint32_t smode = ShiftLSL, uint32_t samount = 0) {
    emit_aluop_reg<op, flg>(rd, 0, op2regimm(rm, smode, samount));
  }
  template <armcg_op op, FlagOperation flg>
  inline void emit_mov_reg_regshift(armcg_regnum rd, armcg_regnum rm, uint32_t smode, uint32_t rs) {
    emit_aluop_reg<op, flg>(rd, 0, op2regreg(rm, smode, rs));
  }
  template <armcg_op op, FlagOperation flg>
  inline void emit_mov_imm(armcg_regnum rd, uint32_t imrot, uint8_t imm8) {
    emit_aluop_imm<op, flg>(rd, 0, op2imm(imm8, imrot));
  }

  // Just a regular operation, no shift, flags set (for easy thumb translation)
  template <armcg_op op>
  inline void emit_alus_reg(armcg_regnum rd, armcg_regnum rn, armcg_regnum rm) {
    emit_aluop_reg<op, SetFlags>(rd, rn, op2regimm(rm, ShiftLSL, 0));
  }
  template <armcg_op op>
  inline void emit_alus_imm(armcg_regnum rd, armcg_regnum rn, uint8_t imm8, uint8_t sa = 0) {
    emit_alu_imm<op, SetFlags>(rd, rn, sa, imm8);
  }

  inline void emit_ldr_imm(armcg_regnum rd, armcg_regnum rb, uint16_t imm12) {
    emit_memop(rd, rb, 0x59, imm12);
  }
  inline void emit_str_imm(armcg_regnum rd, armcg_regnum rb, uint16_t imm12) {
    emit_memop(rd, rb, 0x58, imm12);
  }
  inline void emit_ldr_reg(armcg_regnum rd, armcg_regnum rb, armcg_regnum rm, uint32_t smode, uint32_t samount) {
    emit_memop(rd, rb, 0x79, op2regimm(rm, smode, samount));
  }
  inline void emit_str_reg(armcg_regnum rd, armcg_regnum rb, armcg_regnum rm, uint32_t smode, uint32_t samount) {
    emit_memop(rd, rb, 0x78, op2regimm(rm, smode, samount));
  }

  inline void emit_stmdb(armcg_regnum breg, uint16_t reglist) {
    emit_ldmstm<false, true, false, true>(breg, reglist);
  }
  inline void emit_ldmia(armcg_regnum breg, uint16_t reglist) {
    emit_ldmstm<true, true, true, false>(breg, reglist);
  }

  // Other instructions
  inline void emit_movw(armcg_regnum rd, uint16_t imm16) {
    emit_inst(0xE, (rd << 12) | (imm16 & 0xFFF) | ((imm16 << 4) & 0xF0000) | 0x0300000);
  }
  inline void emit_movt(armcg_regnum rd, uint16_t imm16) {
    emit_inst(0xE, (rd << 12) | (imm16 & 0xFFF) | ((imm16 << 4) & 0xF0000) | 0x0340000);
  }

  inline void emit_usat_asr(armcg_regnum rd, uint8_t imm, armcg_regnum rs, uint8_t samount) {
    emit_inst(0xE, rs | (samount << 7) | (rd << 12) | (imm << 16) | 0x06E00050);
  }

  inline void emit_blx(armcg_regnum rn) {
    emit_inst(0xE, 0x12FFF30 | rn);
  }
  inline void emit_bx(armcg_regnum rn) {
    emit_inst(0xE, 0x12FFF10 | rn);
  }
  inline void emit_bcond(uint32_t cond, uint32_t offset) {
    emit_inst(cond, (5 << 25) | offset);
  }

  inline void emit_mrs_cpsr(armcg_regnum rd) {
    emit_inst(0xE, 0x010F0000 | (rd << 12));
  }
  inline void emit_msr_cpsr(armcg_regnum rs, uint8_t mask) {
    emit_inst(0xE, rs | 0x0120F000 | (mask << 16));
  }

  template <armcg_mulopc opc, FlagOperation flg>
  inline void emit_mull(armcg_regnum rdlo, armcg_regnum rdhi, armcg_regnum rn, armcg_regnum rm) {
    emit_inst(0xE, 0x90 | rn | (rm << 8) | (rdlo << 12) | (rdhi << 16) | (flg == SetFlags ? (1<<20) : 0) | (opc << 21));
  }
  template <FlagOperation flg>
  inline void emit_mla(armcg_regnum rd, armcg_regnum rm, armcg_regnum rs, armcg_regnum rn) {
    emit_inst(0xE, 0x90 | rm | (rs << 8) | (rn << 12) | (rd << 16) | (flg == SetFlags ? (1<<20) : 0) | (armgc_mla << 21));
  }
  template <FlagOperation flg>
  inline void emit_mul(armcg_regnum rd, armcg_regnum rm, armcg_regnum rs) {
    emit_inst(0xE, 0x90 | rm | (rs << 8) | (rd << 16) | (flg == SetFlags ? (1<<20) : 0) | (armgc_mul << 21));
  }

};

#endif


