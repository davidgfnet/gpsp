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
} armcg_regnum;

typedef ARMOp armcg_op;

class ARMEmitter : public CodeEmitterBase {
private:

  inline void emit_inst(uint32_t condc, uint32_t inst) {
    *(uint32_t*)this->emit_ptr = (condc << 28) | inst;
    this->emit_ptr += 4;
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

  ARMEmitter(uint8_t *emit_ptr, uint8_t *emit_end)
   : CodeEmitterBase(emit_ptr, emit_end) {}

  // Performs an ALU operation (with/out flag setting) with some immediate shift amount
  template <armcg_op op, FlagOperation flg>
  inline void emit_alu_reg_immshift(uint32_t rd, uint32_t rn, uint32_t rm, uint32_t smode, uint32_t samount) {
    emit_aluop_reg<op, flg>(rd, rn, op2regimm(rm, smode, samount));
  }

  // Performs an ALU operation (with/out flag setting) with some reg shift amount
  template <armcg_op op, FlagOperation flg>
  inline void emit_alu_reg_regshift(uint32_t rd, uint32_t rn, uint32_t rm, uint32_t smode, uint32_t rs) {
    emit_aluop_reg<op, flg>(rd, rn, op2regreg(rm, smode, rs));
  }

  // Performs an ALU operation (with/out flag setting) with some immediate value
  template <armcg_op op, FlagOperation flg>
  inline void emit_alu_imm(uint32_t rd, uint32_t rn, uint32_t imrot, uint8_t imm8) {
    emit_aluop_imm<op, flg>(rd, rn, op2imm(imm8, imrot));
  }

  // 2 Operands (testing), always generates flags.
  template <armcg_op op>
  inline void emit_test_reg_immshift(uint32_t rn, uint32_t rm, uint32_t smode, uint32_t samount) {
    emit_aluop_reg<op, SetFlags>(0, rn, op2regimm(rm, smode, samount));
  }
  template <armcg_op op>
  inline void emit_test_reg_regshift(uint32_t rn, uint32_t rm, uint32_t smode, uint32_t rs) {
    emit_aluop_reg<op, SetFlags>(0, rn, op2regreg(rm, smode, rs));
  }
  template <armcg_op op>
  inline void emit_test_imm(uint32_t rn, uint32_t imrot, uint8_t imm8) {
    emit_aluop_imm<op, SetFlags>(0, rn, op2imm(imm8, imrot));
  }

  // Unary operations, ie. mov/mvn
  template <armcg_op op, FlagOperation flg>
  inline void emit_mov_reg_immshift(uint32_t rd, uint32_t rm, uint32_t smode, uint32_t samount) {
    emit_aluop_reg<op, flg>(rd, 0, op2regimm(rm, smode, samount));
  }
  template <armcg_op op, FlagOperation flg>
  inline void emit_mov_reg_regshift(uint32_t rd, uint32_t rm, uint32_t smode, uint32_t rs) {
    emit_aluop_reg<op, flg>(rd, 0, op2regreg(rm, smode, rs));
  }
  template <armcg_op op, FlagOperation flg>
  inline void emit_mov_imm(uint32_t rd, uint32_t imrot, uint8_t imm8) {
    emit_aluop_imm<op, flg>(rd, 0, op2imm(imm8, imrot));
  }

  // Just a regular operation, no shift, flags set (for easy thumb translation)
  template <armcg_op op>
  inline void emit_alus_reg(uint32_t rd, uint32_t rn, uint32_t rm) {
    emit_aluop_reg<op, SetFlags>(rd, rn, op2regimm(rm, ShiftLSL, 0));
  }
  template <armcg_op op>
  inline void emit_alus_imm(uint32_t rd, uint32_t rn, uint8_t imm8, uint8_t sa = 0) {
    emit_alu_imm<op, SetFlags>(rd, rn, sa, imm8);
  }

};

#endif


