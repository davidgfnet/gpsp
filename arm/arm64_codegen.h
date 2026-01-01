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

  void emit_inst(aa64_opcode opcode, uint32_t opce, uint32_t rd, uint32_t rs, uint32_t extra) {
    *(uint32_t*)this->emit_ptr = (opcode << 24) | ((opce) << 29) |
                                 ((rs) << 5) | (rd) | (extra);
    this->emit_ptr += 4;
  }

  ARM64Emitter(u8 *emit_ptr, u8 *emit_end)
   : CodeEmitterBase(emit_ptr, emit_end) {}

  // Logic instructions
  void aa64_emit_orr(uint32_t rd, uint32_t rs, uint32_t rm) {
    emit_inst(aa64_opcode_logic, 1, rd, rs, rm << 16);
  }
  void aa64_emit_orn(uint32_t rd, uint32_t rs, uint32_t rm) {
    emit_inst(aa64_opcode_logic, 1, rd, rs, (rm << 16) | (1 << 21));
  }
  void aa64_emit_and(uint32_t rd, uint32_t rs, uint32_t rm) {
    emit_inst(aa64_opcode_logic, 0, rd, rs, rm << 16);
  }
  void aa64_emit_ands(uint32_t rd, uint32_t rs, uint32_t rm) {
    emit_inst(aa64_opcode_logic, 3, rd, rs, rm << 16);
  }
  void aa64_emit_bic(uint32_t rd, uint32_t rs, uint32_t rm) {
    emit_inst(aa64_opcode_logic, 0, rd, rs, (rm << 16) | (1 << 21));
  }
  void aa64_emit_xor(uint32_t rd, uint32_t rs, uint32_t rm) {
    emit_inst(aa64_opcode_logic, 2, rd, rs, rm << 16);
  }
  void aa64_emit_mov(uint32_t rd, uint32_t rs) {
    aa64_emit_orr(rd, 31, rs);
  }

  // Logic immediate instructions
  void aa64_emit_andi(uint32_t rd, uint32_t rs, uint32_t immr, uint32_t imms) {
    emit_inst(aa64_opcode_movi, 0, rd, rs, (imms << 10) | (immr << 16));
  }
  void aa64_emit_orri(uint32_t rd, uint32_t rs, uint32_t immr, uint32_t imms) {
    emit_inst(aa64_opcode_movi, 1, rd, rs, (imms << 10) | (immr << 16));
  }
  void aa64_emit_eori(uint32_t rd, uint32_t rs, uint32_t immr, uint32_t imms) {
    emit_inst(aa64_opcode_movi, 2, rd, rs, (imms << 10) | (immr << 16));
  }
  void aa64_emit_andi64(uint32_t rd, uint32_t rs, uint32_t immr, uint32_t imms) {
    emit_inst(aa64_opcode_movi, 4, rd, rs, (imms << 10) | (immr << 16) | (1 << 22));
  }

  // Useful move-immediate instructions using some imms/immr trickery
  // MovZ, clears the highest bits and sets the lower ones
  void aa64_emit_movlo(uint32_t rd, uint32_t imm) {
    emit_inst(aa64_opcode_movi, 2, rd, 0, ((imm & 0xffff) << 5) | (4 << 21));
  }
  // MovZ, clears the lowest bits and sets the higher ones
  void aa64_emit_movhiz(uint32_t rd, uint32_t imm) {
    emit_inst(aa64_opcode_movi, 2, rd, 0, ((imm & 0xffff) << 5) | (5 << 21));
  }
  // MovK, keeps the other (lower) bits
  void aa64_emit_movhi(uint32_t rd, uint32_t imm) {
    emit_inst(aa64_opcode_movi, 3, rd, 0, ((imm & 0xffff) << 5) | (5 << 21));
  }
  // MovN, moves the inverted immediate (for negative numbers)
  void aa64_emit_movne(uint32_t rd, uint32_t imm) {
    emit_inst(aa64_opcode_movi, 0, rd, 0, ((imm & 0xffff) << 5) | (4 << 21));
  }

  // Basic arithmetic instructions (add/sub)
  template <FlagOperation flg>
  void aa64_emit_addi(uint32_t rd, uint32_t rs, uint32_t imm) {
    emit_inst(aa64_opcode_addsubi, flg == NoFlags ? 0 : 1, rd, rs, (imm << 10));
  }
  template <FlagOperation flg>
  void aa64_emit_addi12(uint32_t rd, uint32_t rs, uint32_t imm) {
    emit_inst(aa64_opcode_addsubi, flg == NoFlags ? 0 : 1, rd, rs, (imm << 10) | (1 << 22));
  }
  template <FlagOperation flg>
  void aa64_emit_subi(uint32_t rd, uint32_t rs, uint32_t imm) {
    emit_inst(aa64_opcode_addsubi, flg == NoFlags ? 2 : 3, rd, rs, (imm << 10));
  }
  template <FlagOperation flg>
  void aa64_emit_subi12(uint32_t rd, uint32_t rs, uint32_t imm) {
    emit_inst(aa64_opcode_addsubi, flg == NoFlags ? 2 : 3, rd, rs, (imm << 10) | (1 << 22));
  }

  // More arithmetic instructions
  template <FlagOperation flg>
  void aa64_emit_add(uint32_t rd, uint32_t rs, uint32_t rm) {
    emit_inst(aa64_opcode_addsub, flg == NoFlags ? 0 : 1, rd, rs, (rm << 16));
  }
  template <FlagOperation flg>
  void aa64_emit_sub(uint32_t rd, uint32_t rs, uint32_t rm) {
    emit_inst(aa64_opcode_addsub, flg == NoFlags ? 2 : 3, rd, rs, (rm << 16));
  }

  template <FlagOperation flg>
  void aa64_emit_adc(uint32_t rd, uint32_t rs, uint32_t rm) {
    emit_inst(aa64_opcode_misc, flg == NoFlags ? 0 : 1, rd, rs, (rm << 16));
  }
  template <FlagOperation flg>
  void aa64_emit_sbc(uint32_t rd, uint32_t rs, uint32_t rm) {
    emit_inst(aa64_opcode_misc, flg == NoFlags ? 2 : 3, rd, rs, (rm << 16));
  }

  // Mult/Div
  void aa64_emit_mul(uint32_t rd, uint32_t rn, uint32_t rm) {
    aa64_emit_madd(rd, 31, rn, rm);    // Add zero
  }
  void aa64_emit_sdiv(uint32_t rd, uint32_t rs, uint32_t rm) {
    emit_inst(aa64_opcode_misc, 0, rd, rs, (rm << 16) | 0xC00C00);
  }
  void aa64_emit_madd(uint32_t rd, uint32_t ra, uint32_t rn, uint32_t rm) {
    // rd = ra + rn * rm
    emit_inst(aa64_opcode_mul4, 0, rd, rn, (ra << 10) | ((rm) << 16));
  }
  void aa64_emit_msub(uint32_t rd, uint32_t ra, uint32_t rn, uint32_t rm) {
    // rd = ra - rn * rm
    emit_inst(aa64_opcode_mul4, 0, rd, rn, (ra << 10) | ((rm) << 16) | 0x8000);
  }
  void aa64_emit_smaddl(uint32_t rd, uint32_t ra, uint32_t rn, uint32_t rm) {
    emit_inst(aa64_opcode_mul4, 4, rd, rn, (ra << 10) | (rm << 16) | 0x200000);
  }
  void aa64_emit_umaddl(uint32_t rd, uint32_t ra, uint32_t rn, uint32_t rm) {
    emit_inst(aa64_opcode_mul4, 4, rd, rn, ((ra) << 10) | ((rm) << 16) | 0xA00000);
  }

  // Testing instructions
  void aa64_emit_cmpi(uint32_t rs, uint32_t imm) {
    aa64_emit_subi<SetFlags>(31, rs, imm);
  }

  // Shift/rotation
  void aa64_emit_extr(uint32_t rd, uint32_t rs, uint32_t rm, uint32_t amount) {
    emit_inst(aa64_opcode_bfm, 0, rd, rs, (1 << 23) | ((amount) << 10) | ((rm) << 16));
  }
  void aa64_emit_ubfm(uint32_t rd, uint32_t rs, uint32_t imms, uint32_t immr) {
    emit_inst(aa64_opcode_bfm, 2, rd, rs, ((imms) << 10) | ((immr) << 16));
  }
  void aa64_emit_ubfx(uint32_t rd, uint32_t rs, uint32_t pos, uint32_t size) {
    aa64_emit_ubfm(rd, rs, pos + size - 1, pos);
  }

  void aa64_emit_ror(uint32_t rd, uint32_t rs, uint32_t amount) {
    aa64_emit_extr(rd, rs, rs, amount);
  }
  void aa64_emit_lsr(uint32_t rd, uint32_t rs, uint32_t amount) {
    emit_inst(aa64_opcode_bfm, 2, rd, rs, (31 << 10) | (amount << 16));
  }
  void aa64_emit_lsl(uint32_t rd, uint32_t rs, uint32_t amount) {
    emit_inst(aa64_opcode_bfm, 2, rd, rs, ((31-amount) << 10) | (((32-amount) & 31) << 16));
  }
  void aa64_emit_asr(uint32_t rd, uint32_t rs, uint32_t amount) {
    emit_inst(aa64_opcode_bfm, 0, rd, rs, (31 << 10) | (amount << 16));
  }
  void aa64_emit_rorv(uint32_t rd, uint32_t rs, uint32_t ra) {
    emit_inst(aa64_opcode_misc, 0, rd, rs, (ra << 16) | 0xC02C00);
  }
  void aa64_emit_lslv(uint32_t rd, uint32_t rs, uint32_t ra) {
    emit_inst(aa64_opcode_misc, 0, rd, rs, (ra << 16) | 0xC02000);
  }
  void aa64_emit_lsrv(uint32_t rd, uint32_t rs, uint32_t ra) {
    emit_inst(aa64_opcode_misc, 0, rd, rs, (ra << 16) | 0xC02400);
  }
  void aa64_emit_asrv(uint32_t rd, uint32_t rs, uint32_t ra) {
    emit_inst(aa64_opcode_misc, 0, rd, rs, (ra << 16) | 0xC02800);
  }

  // Misc
  void aa64_emit_adr(uint32_t rd,  uint32_t offset) {
    emit_inst(aa64_opcode_adr, offset & 3, rd, 0, (offset >> 2) & 0x7ffff);
  }
  void aa64_emit_csinc(uint32_t rd,  uint32_t rs, uint32_t rm, aa64_condcode cond) {
    emit_inst(aa64_opcode_misc, 0, rd, rs, 0x800400 | (rm << 16) | (cond << 12));
  }
  void aa64_emit_csinv(uint32_t rd,  uint32_t rs, uint32_t rm, aa64_condcode cond) {
    emit_inst(aa64_opcode_misc, 2, rd, rs, 0x800000 | (rm << 16) | (cond << 12));
  }
  void aa64_emit_cset(uint32_t rd, aa64_condcode cond) {
    aa64_emit_csinc(rd, 31, 31, (aa64_condcode)(cond ^ 1));
  }
  void aa64_emit_csetm(uint32_t rd, aa64_condcode cond) {
    aa64_emit_csinv(rd, 31, 31, (aa64_condcode)(cond ^ 1));
  }
  void aa64_emit_csel(uint32_t rd,  uint32_t rtrue, uint32_t rfalse, aa64_condcode cond) {
    emit_inst(aa64_opcode_misc, 0, rd, rtrue, (1 << 23) | (rfalse << 16) | (cond << 12));
  }
  void aa64_emit_csneg(uint32_t rd,  uint32_t rs, uint32_t rm, aa64_condcode cond) {
    emit_inst(aa64_opcode_misc, 2, rd, rs, 0x800400 | (rm << 16) | (cond << 12));
  }

  // Branches & small branching (bit or register test)
  void aa64_emit_branch(int32_t offset) {
    emit_inst(aa64_opcode_b, 0, 0, 0, (((u32)(offset))) & 0x3ffffff);
  }
  void aa64_emit_brlink(int32_t offset) {
    emit_inst(aa64_opcode_bl, 0, 0, 0, (((u32)(offset))) & 0x3ffffff);
  }
  void aa64_emit_brcond(aa64_condcode cond, int32_t offset) {
    emit_inst(aa64_opcode_bc, 0, (uint32_t)cond, 0, (((u32)(offset))) & 0x3ffffff);
  }

  void aa64_emit_tbz(uint32_t rd, uint32_t bitnum, int32_t offset) {
    emit_inst(aa64_opcode_tbz, 0, rd, 0, ((((u32)(offset)) & 0x3fff) << 5) | (bitnum << 19));
  }
  void aa64_emit_tbnz(uint32_t rd, uint32_t bitnum, int32_t offset) {
    emit_inst(aa64_opcode_tbnz, 0, rd, 0, ((((u32)(offset)) & 0x3fff) << 5) | (bitnum << 19));
  }
  void aa64_emit_cbz(uint32_t rd, int32_t offset) {
    emit_inst(aa64_opcode_cbz, 0, rd, 0, ((((u32)offset) & 0x7ffff)) << 5);
  }
  void aa64_emit_cbnz(uint32_t rd, int32_t offset) {
    emit_inst(aa64_opcode_cbnz, 0, rd, 0, ((((u32)offset) & 0x7ffff)) << 5);
  }

  // 64 bit operations
  void aa64_emit_lsr64(uint32_t rd, uint32_t rs, uint32_t amount) {
    emit_inst(aa64_opcode_bfm, 6, rd, rs, (1 << 22) | (63 << 10) | (amount << 16));
  }
  void aa64_emit_orr_shift64(uint32_t rd, uint32_t rs, uint32_t rm, uint32_t st, uint32_t sa) {
    emit_inst(aa64_opcode_logic, 5, rd, rs, (rm << 16) | (st << 22) | (sa << 10));
  }
  void aa64_emit_merge_regs(uint32_t rd, uint32_t rshi, uint32_t rslo) {
    aa64_emit_orr_shift64(rd, rslo, rshi, 0, 32);
  }

  // Load/store operations
  void aa64_emit_ldr(uint32_t rv, uint32_t rb, uint32_t offset) {
    emit_inst(aa64_opcode_memi, 5, rv, rb, (1 << 22) | (offset << 10));
  }
  void aa64_emit_str(uint32_t rv, uint32_t rb, uint32_t offset) {
    emit_inst(aa64_opcode_memi, 5, rv, rb, (0 << 22) | (offset << 10));
  }

};

#define aa64_br_offset(label)                                                 \
  (((uintptr_t)(label) - (uintptr_t)(this->emit_ptr)) >> 2)                   \

#define aa64_br_offset_from(label, from)                                      \
  (((uintptr_t)(label) - (uintptr_t)(from)) >> 2)                             \

#define aa64_emit_branch_patch(ptr, offset)                                   \
  *(ptr) = (((*(ptr)) & 0xfc000000) | (((u32)(offset)) & 0x3ffffff))          \

#define aa64_emit_brcond_patch(ptr, offset)                                   \
  *(ptr) = (((*(ptr)) & 0xff00001f) | (((((u32)(offset))) & 0x7ffff) << 5))   \


// Unused (TODO: use them to save some insts)
#define aa64_emit_addshift(rd, rs, rm, st, sa) \
  emit_inst(aa64_opcode_addsub, 0, rd, rs, ((rm) << 16) | ((st)<<22) | ((sa)<<10))
#define aa64_emit_ccmpi(rn, immv, flags, cond) \
  emit_inst(aa64_opcode_misc, 3, rn, flags, 0x400800 | ((immv)<<16) | ((cond)<<12))

