/* gameplaySP
 *
 * Copyright (C) 2021 David Guillen Fandos <david@davidgf.net>
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

typedef enum {
  arm64_reg_x0  =  0,
  arm64_reg_x1  =  1,
  arm64_reg_x2  =  2,
  arm64_reg_x3  =  3,
  arm64_reg_x4  =  4,
  arm64_reg_x5  =  5,
  arm64_reg_x6  =  6,
  arm64_reg_x7  =  7,
  arm64_reg_x8  =  8,
  arm64_reg_x9  =  9,
  arm64_reg_x10 = 10,
  arm64_reg_x11 = 11,
  arm64_reg_x12 = 12,
  arm64_reg_x13 = 13,
  arm64_reg_x14 = 14,
  arm64_reg_x15 = 15,
  arm64_reg_x16 = 16,
  arm64_reg_x17 = 17,
  arm64_reg_x18 = 18,
  arm64_reg_x19 = 19,
  arm64_reg_x20 = 20,
  arm64_reg_x21 = 21,
  arm64_reg_x22 = 22,
  arm64_reg_x23 = 23,
  arm64_reg_x24 = 24,
  arm64_reg_x25 = 25,
  arm64_reg_x26 = 26,
  arm64_reg_x27 = 27,
  arm64_reg_x28 = 28,
  arm64_reg_x29 = 29,
  arm64_reg_x30 = 30,
  arm64_reg_lr  = 30,
  arm64_reg_x31 = 31,
  arm64_reg_sp  = 31,
  arm64_reg_zr  = 31,
} arm64_regnum;

typedef enum {
  aa64_opcode_logic      = 0x0A,
  aa64_opcode_addsub     = 0x0B,
  aa64_opcode_adr        = 0x10,
  aa64_opcode_addsubi    = 0x11,
  aa64_opcode_movi       = 0x12,
  aa64_opcode_bfm        = 0x13,
  aa64_opcode_b          = 0x14,
  aa64_opcode_bc         = 0x54,
  aa64_opcode_bl         = 0x94,
  aa64_opcode_memi       = 0x19,
  aa64_opcode_misc       = 0x1A,
  aa64_opcode_mul4       = 0x1B,
  aa64_opcode_cbz        = 0x34,
  aa64_opcode_cbnz       = 0x35,
  aa64_opcode_tbz        = 0x36,
  aa64_opcode_tbnz       = 0x37,
} aa64_opcode;

typedef enum {
  ccode_eq        = 0x0,  /* Equal       Z == 1 */
  ccode_ne        = 0x1,  /* Not Equal   Z == 0 */
  ccode_hs        = 0x2,  /* Carry Set   C == 1 */
  ccode_lo        = 0x3,  /* Carry Clear C == 0 */
  ccode_mi        = 0x4,  /* Minus/Neg   N == 1 */
  ccode_pl        = 0x5,  /* Plus/Pos    N == 0 */
  ccode_vs        = 0x6,  /* Overflow    V == 1 */
  ccode_vc        = 0x7,  /* !Overflow   V == 0 */
  ccode_hi        = 0x8,  /* UGreatThan C && !Z */
  ccode_ls        = 0x9,  /* ULessEqual !C || Z */
  ccode_ge        = 0xA,  /* SGreatEqual N == V */
  ccode_lt        = 0xB,  /* SLessThan   N != V */
  ccode_gt        = 0xC,  /* SLessThan   !Z&N==V  */
  ccode_le        = 0xD,  /* SLessEqual  Z|(N!=V) */
  ccode_al        = 0xE,  /* Always             */
  ccode_nv        = 0xF,  /* Never              */
} aa64_condcode;


class ARM64Emitter : public CodeEmitterBase {
public:

  inline void emit_inst(aa64_opcode opcode, uint32_t opce, uint32_t rd, uint32_t rs, uint32_t extra) {
    *(uint32_t*)this->emit_ptr = (opcode << 24) | ((opce) << 29) |
                                 ((rs) << 5) | (rd) | (extra);
    this->emit_ptr += 4;
  }

  ARM64Emitter(uint8_t *emit_ptr)
   : CodeEmitterBase(emit_ptr) {}

  // Logic instructions
  inline void aa64_emit_orr(arm64_regnum rd, arm64_regnum rs, arm64_regnum rm) {
    emit_inst(aa64_opcode_logic, 1, rd, rs, rm << 16);
  }
  inline void aa64_emit_orn(arm64_regnum rd, arm64_regnum rs, arm64_regnum rm) {
    emit_inst(aa64_opcode_logic, 1, rd, rs, (rm << 16) | (1 << 21));
  }
  inline void aa64_emit_and(arm64_regnum rd, arm64_regnum rs, arm64_regnum rm) {
    emit_inst(aa64_opcode_logic, 0, rd, rs, rm << 16);
  }
  inline void aa64_emit_ands(arm64_regnum rd, arm64_regnum rs, arm64_regnum rm) {
    emit_inst(aa64_opcode_logic, 3, rd, rs, rm << 16);
  }
  inline void aa64_emit_bic(arm64_regnum rd, arm64_regnum rs, arm64_regnum rm) {
    emit_inst(aa64_opcode_logic, 0, rd, rs, (rm << 16) | (1 << 21));
  }
  inline void aa64_emit_xor(arm64_regnum rd, arm64_regnum rs, arm64_regnum rm) {
    emit_inst(aa64_opcode_logic, 2, rd, rs, rm << 16);
  }
  inline void aa64_emit_mov(arm64_regnum rd, arm64_regnum rs) {
    aa64_emit_orr(rd, arm64_reg_zr, rs);
  }
  inline void aa64_emit_tst(arm64_regnum rs, arm64_regnum rm) {
    aa64_emit_ands(arm64_reg_zr, rs, rm);
  }

  // Logic immediate instructions
  inline void aa64_emit_andi(arm64_regnum rd, arm64_regnum rs, uint32_t immr, uint32_t imms) {
    emit_inst(aa64_opcode_movi, 0, rd, rs, (imms << 10) | (immr << 16));
  }
  inline void aa64_emit_orri(arm64_regnum rd, arm64_regnum rs, uint32_t immr, uint32_t imms) {
    emit_inst(aa64_opcode_movi, 1, rd, rs, (imms << 10) | (immr << 16));
  }
  inline void aa64_emit_eori(arm64_regnum rd, arm64_regnum rs, uint32_t immr, uint32_t imms) {
    emit_inst(aa64_opcode_movi, 2, rd, rs, (imms << 10) | (immr << 16));
  }
  inline void aa64_emit_andi64(arm64_regnum rd, arm64_regnum rs, uint32_t immr, uint32_t imms) {
    emit_inst(aa64_opcode_movi, 4, rd, rs, (imms << 10) | (immr << 16) | (1 << 22));
  }

  // Useful move-immediate instructions using some imms/immr trickery
  // MovZ, clears the highest bits and sets the lower ones
  inline void aa64_emit_movlo(arm64_regnum rd, uint32_t imm) {
    emit_inst(aa64_opcode_movi, 2, rd, 0, ((imm & 0xffff) << 5) | (4 << 21));
  }
  // MovZ, clears the lowest bits and sets the higher ones
  inline void aa64_emit_movhiz(arm64_regnum rd, uint32_t imm) {
    emit_inst(aa64_opcode_movi, 2, rd, 0, ((imm & 0xffff) << 5) | (5 << 21));
  }
  // MovK, keeps the other (lower) bits
  inline void aa64_emit_movhi(arm64_regnum rd, uint32_t imm) {
    emit_inst(aa64_opcode_movi, 3, rd, 0, ((imm & 0xffff) << 5) | (5 << 21));
  }
  // MovN, moves the inverted immediate (for negative numbers)
  inline void aa64_emit_movne(arm64_regnum rd, uint32_t imm) {
    emit_inst(aa64_opcode_movi, 0, rd, 0, ((imm & 0xffff) << 5) | (4 << 21));
  }

  // Basic arithmetic instructions (add/sub)
  template <FlagOperation flg>
  inline void aa64_emit_addi(arm64_regnum rd, arm64_regnum rs, uint32_t imm) {
    emit_inst(aa64_opcode_addsubi, flg == NoFlags ? 0 : 1, rd, rs, (imm << 10));
  }
  template <FlagOperation flg>
  inline void aa64_emit_addi12(arm64_regnum rd, arm64_regnum rs, uint32_t imm) {
    emit_inst(aa64_opcode_addsubi, flg == NoFlags ? 0 : 1, rd, rs, (imm << 10) | (1 << 22));
  }
  template <FlagOperation flg>
  inline void aa64_emit_subi(arm64_regnum rd, arm64_regnum rs, uint32_t imm) {
    emit_inst(aa64_opcode_addsubi, flg == NoFlags ? 2 : 3, rd, rs, (imm << 10));
  }
  template <FlagOperation flg>
  inline void aa64_emit_subi12(arm64_regnum rd, arm64_regnum rs, uint32_t imm) {
    emit_inst(aa64_opcode_addsubi, flg == NoFlags ? 2 : 3, rd, rs, (imm << 10) | (1 << 22));
  }

  // More arithmetic instructions
  template <FlagOperation flg>
  inline void aa64_emit_add(arm64_regnum rd, arm64_regnum rs, arm64_regnum rm) {
    emit_inst(aa64_opcode_addsub, flg == NoFlags ? 0 : 1, rd, rs, (rm << 16));
  }
  template <FlagOperation flg>
  inline void aa64_emit_sub(arm64_regnum rd, arm64_regnum rs, arm64_regnum rm) {
    emit_inst(aa64_opcode_addsub, flg == NoFlags ? 2 : 3, rd, rs, (rm << 16));
  }

  template <FlagOperation flg>
  inline void aa64_emit_adc(arm64_regnum rd, arm64_regnum rs, arm64_regnum rm) {
    emit_inst(aa64_opcode_misc, flg == NoFlags ? 0 : 1, rd, rs, (rm << 16));
  }
  template <FlagOperation flg>
  inline void aa64_emit_sbc(arm64_regnum rd, arm64_regnum rs, arm64_regnum rm) {
    emit_inst(aa64_opcode_misc, flg == NoFlags ? 2 : 3, rd, rs, (rm << 16));
  }

  // Mult/Div
  inline void aa64_emit_mul(arm64_regnum rd, arm64_regnum rn, arm64_regnum rm) {
    aa64_emit_madd(rd, arm64_reg_zr, rn, rm);    // Add zero
  }
  inline void aa64_emit_sdiv(arm64_regnum rd, arm64_regnum rs, arm64_regnum rm) {
    emit_inst(aa64_opcode_misc, 0, rd, rs, (rm << 16) | 0xC00C00);
  }
  inline void aa64_emit_madd(arm64_regnum rd, arm64_regnum ra, arm64_regnum rn, arm64_regnum rm) {
    // rd = ra + rn * rm
    emit_inst(aa64_opcode_mul4, 0, rd, rn, (ra << 10) | ((rm) << 16));
  }
  inline void aa64_emit_msub(arm64_regnum rd, arm64_regnum ra, arm64_regnum rn, arm64_regnum rm) {
    // rd = ra - rn * rm
    emit_inst(aa64_opcode_mul4, 0, rd, rn, (ra << 10) | ((rm) << 16) | 0x8000);
  }
  inline void aa64_emit_smaddl(arm64_regnum rd, arm64_regnum ra, arm64_regnum rn, arm64_regnum rm) {
    emit_inst(aa64_opcode_mul4, 4, rd, rn, (ra << 10) | (rm << 16) | 0x200000);
  }
  inline void aa64_emit_umaddl(arm64_regnum rd, arm64_regnum ra, arm64_regnum rn, arm64_regnum rm) {
    emit_inst(aa64_opcode_mul4, 4, rd, rn, ((ra) << 10) | ((rm) << 16) | 0xA00000);
  }

  // Testing instructions
  inline void aa64_emit_cmpi(arm64_regnum rs, uint32_t imm) {
    aa64_emit_subi<SetFlags>(arm64_reg_zr, rs, imm);
  }

  // Shift/rotation
  inline void aa64_emit_extr(arm64_regnum rd, arm64_regnum rs, arm64_regnum rm, uint32_t amount) {
    emit_inst(aa64_opcode_bfm, 0, rd, rs, (1 << 23) | ((amount) << 10) | ((rm) << 16));
  }
  inline void aa64_emit_ubfm(arm64_regnum rd, arm64_regnum rs, uint32_t imms, uint32_t immr) {
    emit_inst(aa64_opcode_bfm, 2, rd, rs, ((imms) << 10) | ((immr) << 16));
  }
  inline void aa64_emit_ubfx(arm64_regnum rd, arm64_regnum rs, uint32_t pos, uint32_t size) {
    aa64_emit_ubfm(rd, rs, pos + size - 1, pos);
  }

  inline void aa64_emit_ror(arm64_regnum rd, arm64_regnum rs, uint32_t amount) {
    aa64_emit_extr(rd, rs, rs, amount);
  }
  inline void aa64_emit_lsr(arm64_regnum rd, arm64_regnum rs, uint32_t amount) {
    emit_inst(aa64_opcode_bfm, 2, rd, rs, (31 << 10) | (amount << 16));
  }
  inline void aa64_emit_lsl(arm64_regnum rd, arm64_regnum rs, uint32_t amount) {
    emit_inst(aa64_opcode_bfm, 2, rd, rs, ((31-amount) << 10) | (((32-amount) & 31) << 16));
  }
  inline void aa64_emit_asr(arm64_regnum rd, arm64_regnum rs, uint32_t amount) {
    emit_inst(aa64_opcode_bfm, 0, rd, rs, (31 << 10) | (amount << 16));
  }
  inline void aa64_emit_rorv(arm64_regnum rd, arm64_regnum rs, arm64_regnum ra) {
    emit_inst(aa64_opcode_misc, 0, rd, rs, (ra << 16) | 0xC02C00);
  }
  inline void aa64_emit_lslv(arm64_regnum rd, arm64_regnum rs, arm64_regnum ra) {
    emit_inst(aa64_opcode_misc, 0, rd, rs, (ra << 16) | 0xC02000);
  }
  inline void aa64_emit_lsrv(arm64_regnum rd, arm64_regnum rs, arm64_regnum ra) {
    emit_inst(aa64_opcode_misc, 0, rd, rs, (ra << 16) | 0xC02400);
  }
  inline void aa64_emit_asrv(arm64_regnum rd, arm64_regnum rs, arm64_regnum ra) {
    emit_inst(aa64_opcode_misc, 0, rd, rs, (ra << 16) | 0xC02800);
  }

  // Misc
  inline void aa64_emit_adr(arm64_regnum rd,  uint32_t offset) {
    emit_inst(aa64_opcode_adr, offset & 3, rd, 0, (offset >> 2) & 0x7ffff);
  }
  inline void aa64_emit_csinc(arm64_regnum rd,  arm64_regnum rs, arm64_regnum rm, aa64_condcode cond) {
    emit_inst(aa64_opcode_misc, 0, rd, rs, 0x800400 | (rm << 16) | (cond << 12));
  }
  inline void aa64_emit_csinv(arm64_regnum rd,  arm64_regnum rs, arm64_regnum rm, aa64_condcode cond) {
    emit_inst(aa64_opcode_misc, 2, rd, rs, 0x800000 | (rm << 16) | (cond << 12));
  }
  inline void aa64_emit_cset(arm64_regnum rd, aa64_condcode cond) {
    aa64_emit_csinc(rd, arm64_reg_zr, arm64_reg_zr, (aa64_condcode)(cond ^ 1));
  }
  inline void aa64_emit_csetm(arm64_regnum rd, aa64_condcode cond) {
    aa64_emit_csinv(rd, arm64_reg_zr, arm64_reg_zr, (aa64_condcode)(cond ^ 1));
  }
  inline void aa64_emit_csel(arm64_regnum rd,  arm64_regnum rtrue, arm64_regnum rfalse, aa64_condcode cond) {
    emit_inst(aa64_opcode_misc, 0, rd, rtrue, (1 << 23) | (rfalse << 16) | (cond << 12));
  }
  inline void aa64_emit_csneg(arm64_regnum rd,  arm64_regnum rs, arm64_regnum rm, aa64_condcode cond) {
    emit_inst(aa64_opcode_misc, 2, rd, rs, 0x800400 | (rm << 16) | (cond << 12));
  }

  // Branches & small branching (bit or register test)
  inline void aa64_emit_branch(int32_t offset) {
    emit_inst(aa64_opcode_b, 0, 0, 0, (((uint32_t)(offset))) & 0x3ffffff);
  }
  inline void aa64_emit_brlink(int32_t offset) {
    emit_inst(aa64_opcode_bl, 0, 0, 0, (((uint32_t)(offset))) & 0x3ffffff);
  }
  inline void aa64_emit_brcond(aa64_condcode cond, int32_t offset) {
    emit_inst(aa64_opcode_bc, 0, (uint32_t)cond, 0, ((uint32_t)(offset) & 0x7ffff) << 5);
  }

  inline void aa64_emit_tbz(arm64_regnum rd, uint32_t bitnum, int32_t offset) {
    emit_inst(aa64_opcode_tbz, 0, rd, 0, ((((uint32_t)(offset)) & 0x3fff) << 5) | (bitnum << 19));
  }
  inline void aa64_emit_tbnz(arm64_regnum rd, uint32_t bitnum, int32_t offset) {
    emit_inst(aa64_opcode_tbnz, 0, rd, 0, ((((uint32_t)(offset)) & 0x3fff) << 5) | (bitnum << 19));
  }
  inline void aa64_emit_cbz(arm64_regnum rd, int32_t offset) {
    emit_inst(aa64_opcode_cbz, 0, rd, 0, ((((uint32_t)offset) & 0x7ffff)) << 5);
  }
  inline void aa64_emit_cbnz(arm64_regnum rd, int32_t offset) {
    emit_inst(aa64_opcode_cbnz, 0, rd, 0, ((((uint32_t)offset) & 0x7ffff)) << 5);
  }

  // 64 bit operations
  inline void aa64_emit_lsr64(arm64_regnum rd, arm64_regnum rs, uint32_t amount) {
    emit_inst(aa64_opcode_bfm, 6, rd, rs, (1 << 22) | (63 << 10) | (amount << 16));
  }
  inline void aa64_emit_orr_shift64(arm64_regnum rd, arm64_regnum rs, arm64_regnum rm, uint32_t st, uint32_t sa) {
    emit_inst(aa64_opcode_logic, 5, rd, rs, (rm << 16) | (st << 22) | (sa << 10));
  }
  inline void aa64_emit_merge_regs(arm64_regnum rd, arm64_regnum rshi, arm64_regnum rslo) {
    aa64_emit_orr_shift64(rd, rslo, rshi, 0, 32);
  }

  // Load/store operations
  inline void aa64_emit_ldr(arm64_regnum rv, arm64_regnum rb, uint32_t offset) {
    emit_inst(aa64_opcode_memi, 5, rv, rb, (1 << 22) | (offset << 10));
  }
  inline void aa64_emit_str(arm64_regnum rv, arm64_regnum rb, uint32_t offset) {
    emit_inst(aa64_opcode_memi, 5, rv, rb, (0 << 22) | (offset << 10));
  }

};

#define aa64_br_offset(label)                                                 \
  (((uintptr_t)(label) - (uintptr_t)(this->emit_ptr)) >> 2)                   \

#define aa64_br_offset_from(label, from)                                      \
  (((uintptr_t)(label) - (uintptr_t)(from)) >> 2)                             \

#define aa64_emit_branch_patch(ptr, offset)                                   \
  *(ptr) = (((*(ptr)) & 0xfc000000) | (((uint32_t)(offset)) & 0x3ffffff))

#define aa64_emit_brcond_patch(ptr, offset)                                   \
  *(ptr) = (((*(ptr)) & 0xff00001f) | (((((uint32_t)(offset))) & 0x7ffff) << 5))


// Unused (TODO: use them to save some insts)
#define aa64_emit_addshift(rd, rs, rm, st, sa) \
  emit_inst(aa64_opcode_addsub, 0, rd, rs, ((rm) << 16) | ((st)<<22) | ((sa)<<10))
#define aa64_emit_ccmpi(rn, immv, flags, cond) \
  emit_inst(aa64_opcode_misc, 3, rn, flags, 0x400800 | ((immv)<<16) | ((cond)<<12))

