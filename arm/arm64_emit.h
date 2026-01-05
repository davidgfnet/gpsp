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

#ifndef ARM64_EMIT_H
#define ARM64_EMIT_H

#include "arm64_codegen.h"

/* This is a fork of the MIPS dynarec, since A64 has 32 regs as well and
   does not map great to the armv4 instruction set. Also flexible operand
   is fairly limited and cannot map to armv4 well.
   All flags are kept in registers and loaded/restored as needed. */

extern "C" {
  u32 a64_update_gba(u32 pc);

  // Although these are defined as a function, don't call them as
  // such (jump to it instead)
  void a64_indirect_branch_arm(u32 address);
  void a64_indirect_branch_thumb(u32 address);
  void a64_indirect_branch_dual(u32 address);

  u32 execute_read_cpsr();
  u32 execute_read_spsr();
  void execute_swi(u32 pc);
  void a64_cheat_hook(void);

  u32 execute_spsr_restore(u32 address);
  void execute_store_cpsr(u32 new_cpsr, u32 store_mask);
  void execute_store_spsr(u32 new_spsr, u32 store_mask);
  u32 execute_spsr_restore_body(u32 address);

  void execute_aligned_store32(u32 addr, u32 data);
  u32 execute_aligned_load32(u32 addr);

  u32 execute_arm_translate_internal(u32 cycles, void *regptr);
}

template <typename memtype> inline uintptr_t call_ldr_handler();
template <typename memtype> inline uintptr_t call_str_handler();

template <> inline uintptr_t call_ldr_handler<u32>() { return (uintptr_t)execute_load_u32; }
template <> inline uintptr_t call_ldr_handler<u16>() { return (uintptr_t)execute_load_u16; }
template <> inline uintptr_t call_ldr_handler<u8>()  { return (uintptr_t)execute_load_u8 ; }
template <> inline uintptr_t call_ldr_handler<s16>() { return (uintptr_t)execute_load_s16; }
template <> inline uintptr_t call_ldr_handler<s8>()  { return (uintptr_t)execute_load_s8 ; }

template <> inline uintptr_t call_str_handler<u32>() { return (uintptr_t)execute_store_u32; }
template <> inline uintptr_t call_str_handler<u16>() { return (uintptr_t)execute_store_u16; }
template <> inline uintptr_t call_str_handler<u8>()  { return (uintptr_t)execute_store_u8 ; }


#define reg_res     arm64_reg_x0
#define reg_a0      arm64_reg_x0
#define reg_a1      arm64_reg_x1
#define reg_a2      arm64_reg_x2
#define reg_temp    arm64_reg_x3
#define reg_temp2   arm64_reg_x4
#define reg_save0   arm64_reg_x19  // saved
#define reg_base    arm64_reg_x20  // saved
#define reg_cycles  arm64_reg_x21  // saved
#define reg_c_cache arm64_reg_x22  // saved
#define reg_v_cache arm64_reg_x23  // saved
#define reg_z_cache arm64_reg_x24  // saved
#define reg_n_cache arm64_reg_x25  // saved

#define reg_r0      arm64_reg_x6   // temporary
#define reg_r1      arm64_reg_x7   // temporary
#define reg_r2      arm64_reg_x8   // temporary
#define reg_r3      arm64_reg_x9   // temporary
#define reg_r4      arm64_reg_x10  // temporary
#define reg_r5      arm64_reg_x11  // temporary
#define reg_r6      arm64_reg_x12  // temporary
#define reg_r7      arm64_reg_x13  // temporary
#define reg_r8      arm64_reg_x14  // temporary
#define reg_r9      arm64_reg_x15  // temporary
#define reg_r10     arm64_reg_x16  // temporary
#define reg_r11     arm64_reg_x17  // temporary
#define reg_r12     arm64_reg_x26  // saved
#define reg_r13     arm64_reg_x27  // saved
#define reg_r14     arm64_reg_x28  // saved
#define reg_pc      arm64_reg_x29  // saved (points to block_pc)

#define reg_zero    arm64_reg_sp  // Careful it's also SP

// Writing to r15 goes straight to a0, to be chained with other ops
const arm64_regnum arm_to_a64_reg[] = {
  reg_r0, reg_r1, reg_r2, reg_r3, reg_r4, reg_r5, reg_r6, reg_r7,
  reg_r8, reg_r9, reg_r10, reg_r11, reg_r12, reg_r13, reg_r14, reg_a0,
};


#define generate_store_reg(ireg, reg_index)                                   \
  aa64_emit_mov(arm_to_a64_reg[reg_index], ireg)                              \

#define generate_function_call(function_location)                             \
  aa64_emit_brlink(aa64_br_offset(function_location));                        \

/* Patches ARM-mode conditional branches */
#define generate_branch_patch_conditional(dest, label)                        \
  aa64_emit_brcond_patch(((u32*)dest), aa64_br_offset_from(label, dest))

#define emit_branch_filler(writeback_location)                                \
  (writeback_location) = this->emit_ptr;                                      \
  aa64_emit_branch(0);                                                        \

#define generate_branch_patch_unconditional(dest, target)                     \
  aa64_emit_branch_patch((u32*)dest, aa64_br_offset_from(target, dest))       \

#define generate_branch_no_cycle_update(writeback_location, new_pc)           \
  if(pc == idle_loop_target_pc) {                                             \
    generate_load_imm(reg_cycles, 0);                                         \
    generate_load_pc(reg_a0, new_pc);                                         \
    generate_function_call(a64_update_gba);                                   \
    emit_branch_filler(writeback_location);                                   \
  } else {                                                                    \
    aa64_emit_tbnz(reg_cycles, 31, 2);                                        \
    emit_branch_filler(writeback_location);                                   \
    aa64_emit_movlo(reg_a0, new_pc);                                          \
    aa64_emit_movhi(reg_a0, ((new_pc) >> 16));                                \
    generate_function_call(a64_update_gba);                                   \
    aa64_emit_branch(-4);                                                     \
  }                                                                           \

#define generate_branch_cycle_update(writeback_location, new_pc)              \
  generate_cycle_update(cycle_count);                                         \
  generate_branch_no_cycle_update(writeback_location, new_pc)                 \

// a0 holds the destination

#define generate_indirect_branch_cycle_update(type)                           \
  generate_cycle_update(cycle_count);                                         \
  generate_indirect_branch_no_cycle_update(type)                              \

#define generate_indirect_branch_no_cycle_update(type)                        \
  aa64_emit_branch(aa64_br_offset(a64_indirect_branch_##type));               \

#define check_store_reg_pc_no_flags(reg_index)                                \
  if(reg_index == REG_PC) {                                                   \
    generate_indirect_branch_arm();                                           \
  }                                                                           \

#define check_store_reg_pc_flags(reg_index)                                   \
  if(reg_index == REG_PC) {                                                   \
    generate_function_call(execute_spsr_restore);                             \
    generate_indirect_branch_dual();                                          \
  }                                                                           \

#define generate_indirect_branch_arm() {                                      \
  if(condition == 0x0E) {                                                     \
    generate_indirect_branch_cycle_update(arm);                               \
  } else {                                                                    \
    generate_indirect_branch_no_cycle_update(arm);                            \
  }                                                                           \
}                                                                             \

#define generate_indirect_branch_dual() {                                     \
  if(condition == 0x0E) {                                                     \
    generate_indirect_branch_cycle_update(dual);                              \
  } else {                                                                    \
    generate_indirect_branch_no_cycle_update(dual);                           \
  }                                                                           \
}                                                                             \


// It should be okay to still generate result flags, spsr will overwrite them.
// This is pretty infrequent (returning from interrupt handlers, et al) so
// probably not worth optimizing for.

u32 execute_spsr_restore_body(u32 address) {
  set_cpu_mode(cpu_modes[reg[REG_CPSR] & 0xF]);
  if((io_registers[REG_IE] & io_registers[REG_IF]) &&
   io_registers[REG_IME] && ((reg[REG_CPSR] & 0x80) == 0))
  {
    REG_MODE(MODE_IRQ)[6] = address + 4;
    REG_SPSR(MODE_IRQ) = reg[REG_CPSR];
    reg[REG_CPSR] = 0xD2;
    address = 0x00000018;
    set_cpu_mode(MODE_IRQ);
  }

  if(reg[REG_CPSR] & 0x20)
    address |= 0x01;

  return address;
}

#define check_store_reg_pc_thumb(_rd)                                         \
  if(_rd == REG_PC) {                                                         \
    generate_indirect_branch_cycle_update(thumb);                             \
  }                                                                           \

#define generate_branch_filler(condition_code, writeback_location)            \
  (writeback_location) = this->emit_ptr;                                      \
  aa64_emit_brcond(condition_code, 0);                                        \


inline bool isimm12(u32 imm) {
  return (imm & 0xFFFFF000) == 0;
}

inline bool isimm24(u32 imm) {
  return (imm & 0xFF000000) == 0;
}

inline bool isimmhi12(u32 imm) {
  return (imm & 0xFF000FFF) == 0;
}

class CodeEmitter : public ARM64Emitter {
public:
  CodeEmitter(u8 *emit_ptr, u8 *emit_end, u32 pc)
   : ARM64Emitter(emit_ptr, emit_end), block_pc(pc) {}

  u32 block_pc;              // PC address for the block base

  static unsigned block_prologue_size() { return 0; }

  inline void emit_block_prologue() {
    generate_load_imm(reg_pc, this->block_pc);
  }

  inline void generate_load_pc(arm64_regnum rd, uint32_t pc) {
    s32 pc_delta = pc - this->block_pc;
    if (pc_delta >= 0) {
      if (pc_delta < 4096)
        aa64_emit_addi<NoFlags>(rd, reg_pc, pc_delta);
      else
        generate_load_imm(rd, pc);
    } else {
      if (pc_delta >= -4096)
        aa64_emit_subi<NoFlags>(rd, reg_pc, -pc_delta);
      else
        generate_load_imm(rd, pc);
    }
  }

  // Register allocation (for registers that could contain PC)
  inline arm64_regnum load_alloc_reg(u32 regn, arm64_regnum tmp_reg, u32 pcvalue) {
    if (regn != REG_PC)
      return arm_to_a64_reg[regn];

    generate_load_pc(tmp_reg, pcvalue);
    return tmp_reg;
  }

  // Forces a register load!
  inline void force_load_reg(u32 regn, arm64_regnum outreg, u32 pcvalue) {
    if (regn == REG_PC)
      generate_load_pc(outreg, pcvalue);
    else
      aa64_emit_mov(outreg, arm_to_a64_reg[regn]);
  }

  inline arm64_regnum store_alloc_reg(u32 regn, arm64_regnum tmp_reg) {
    if (regn == REG_PC)
      return tmp_reg;
    return arm_to_a64_reg[regn];
  }

  inline void load_alloc_reg_lsb(u32 regn, arm64_regnum native_reg, u32 pcvalue) {
    if (regn == REG_PC)
      aa64_emit_movlo(native_reg, (pcvalue & 0xFF));
    else
      aa64_emit_andi(native_reg, arm_to_a64_reg[regn], 0, 7); /* 0xFF */
  }

  inline void load_c_flag() {
    aa64_emit_movne(reg_temp, 0);
    aa64_emit_add<SetFlags>(reg_temp, reg_temp, reg_c_cache);
  }

  template <FlagOperation flgmode>
  inline void update_nz_flags(const BaseInst & it, arm64_regnum reg) {
    if (flgmode == SetFlags) {
      if (it.gen_flag_n())
        aa64_emit_lsr(reg_n_cache, reg, 31);

      if (it.gen_flag_z()) {
        aa64_emit_cmpi(reg, 0);
        aa64_emit_cset(reg_z_cache, ccode_eq);
      }
    }
  }

  template <FlagOperation flgmode>
  inline void update_nzcv_arith_flags(const BaseInst & it) {
    if (flgmode == SetFlags) {
      if (it.gen_flag_c())
        aa64_emit_cset(reg_c_cache, ccode_hs);
      if (it.gen_flag_v())
        aa64_emit_cset(reg_v_cache, ccode_vs);
      if (it.gen_flag_n())
        aa64_emit_cset(reg_n_cache, ccode_mi);
      if (it.gen_flag_z())
        aa64_emit_cset(reg_z_cache, ccode_eq);
    }
  }

  template <FlagOperation flgmode>
  inline void upd_nz_flags_imm(const ARMInst & it, u32 imm) {
    if (flgmode == SetFlags) {
      if (it.gen_flag_z())
        aa64_emit_movlo(reg_z_cache, (imm ? 0 : 1));
      if (it.gen_flag_n())
        aa64_emit_movlo(reg_n_cache, (imm >> 31));
    }
  }

  inline void generate_load_imm(arm64_regnum rd, uint32_t imm) {
    if ((s32)(imm) < 0 && (s32)(imm) >= -65536)
      aa64_emit_movne(rd, ~imm);       // immediate like 0xffffxxxx
    else if ((imm & 0xffff) == 0)
      aa64_emit_movhiz(rd, imm >> 16); // immediate like 0xxxxx0000
    else {
      aa64_emit_movlo(rd, imm);
      if (imm >= (1 << 16))
        aa64_emit_movhi(rd, imm >> 16);
    }
  }

  void aa64_emit_addsubi(arm64_regnum dreg, arm64_regnum sreg, int imm) {
    if (imm >= 0)
      aa64_emit_addi<NoFlags>(dreg, sreg, imm);
    else
      aa64_emit_subi<NoFlags>(dreg, sreg, -imm);
  }

  // Adds an arbitrarily big immediate (honoring flag setting if needed)
  template <FlagOperation flg>
  void aa64_emit_addlimm(arm64_regnum rd, arm64_regnum rs, uint32_t imm) {
    // Adds a long immediate using a few insts is possible.
    if (isimm12(imm))
      aa64_emit_addi<flg>(rd, rs, imm);
    else if (isimmhi12(imm))
      aa64_emit_addi12<flg>(rd, rs, (imm >> 12));
    else if (flg == NoFlags && isimm24(imm)) {
      aa64_emit_addi<NoFlags>(rd, rs, (imm & 0xFFF));
      aa64_emit_addi12<NoFlags>(rd, rd, ((imm >> 12) & 0xFFF));
    }
    else {
      generate_load_imm(reg_temp, imm);
      aa64_emit_add<flg>(rd, rs, reg_temp);
    }
  }

  template <FlagOperation flg>
  void aa64_emit_sublimm(arm64_regnum rd, arm64_regnum rs, uint32_t imm) {
    // Subss a long immediate using a few insts is possible.
    if (isimm12(imm))
      aa64_emit_subi<flg>(rd, rs, imm);
    else if (isimmhi12(imm))
      aa64_emit_subi12<flg>(rd, rs, (imm >> 12));
    else if (flg == NoFlags && isimm24(imm)) {
      aa64_emit_subi<NoFlags>(rd, rs, (imm & 0xFFF));
      aa64_emit_subi12<NoFlags>(rd, rd, ((imm >> 12) & 0xFFF));
    }
    else {
      generate_load_imm(reg_temp, imm);
      aa64_emit_sub<flg>(rd, rs, reg_temp);
    }
  }

  inline void generate_cycle_update(u32 & cycle_count) {
    if (cycle_count)
      aa64_emit_sublimm<NoFlags>(reg_cycles, reg_cycles, cycle_count);
    cycle_count = 0;
  }

  template <CPUInstMode cm>
  inline void generate_translation_gate(u32 pc) {
    generate_load_pc(reg_a0, pc);
    if (cm == ModeARM)
      aa64_emit_branch(aa64_br_offset(a64_indirect_branch_arm));
    else
      aa64_emit_branch(aa64_br_offset(a64_indirect_branch_thumb));
  }

  inline void emit_cycle_update(u32 & cycle_count) {
    generate_cycle_update(cycle_count);
  }

  template <CPUInstMode cm>
  inline void emit_cheat_hook() {
    generate_function_call(a64_cheat_hook);
  }

  inline void emit_load_const_pool(u32 regn, u32 value) {
    generate_load_imm(arm_to_a64_reg[regn], (value));
  }

  inline void arm_conditional_block_header(u32 condition, u32 & cycle_count, u8 * & backpatch_address) {
    generate_cycle_update(cycle_count);
    backpatch_address = emit_opp_condbranch((ARMCondCode)condition);  // TODO: use ARMCondCode as type natively
  }


  // Condition code generation
  inline u8 *emit_opp_condbranch(ARMCondCode ccode) {
    // TODO Take reg num as input.
    // We emit a branch that branches on the opposite condition.
    // Returns the patching address (so the branch offset can be filled)
    u8 *ret = NULL;

    switch (ccode) {
    case CondEQ:
      ret = this->emit_ptr;
      aa64_emit_cbz(reg_z_cache, 0);
      break;
    case CondNE:
      ret = this->emit_ptr;
      aa64_emit_cbnz(reg_z_cache, 0);
      break;
    case CondCS:
      ret = this->emit_ptr;
      aa64_emit_cbz(reg_c_cache, 0);
      break;
    case CondCC:
      ret = this->emit_ptr;
      aa64_emit_cbnz(reg_c_cache, 0);
      break;
    case CondMI:
      ret = this->emit_ptr;
      aa64_emit_cbz(reg_n_cache, 0);
      break;
    case CondPL:
      ret = this->emit_ptr;
      aa64_emit_cbnz(reg_n_cache, 0);
      break;
    case CondVS:
      ret = this->emit_ptr;
      aa64_emit_cbz(reg_v_cache, 0);
      break;
    case CondVC:
      ret = this->emit_ptr;
      aa64_emit_cbnz(reg_v_cache, 0);
      break;
    case CondHI:
      aa64_emit_eori(reg_temp, reg_c_cache, 0, 0);  /* imm=1 */
      aa64_emit_orr(reg_temp, reg_temp, reg_z_cache);
      ret = this->emit_ptr;
      aa64_emit_cbnz(reg_temp, 0);
      break;
    case CondLS:
      aa64_emit_eori(reg_temp, reg_c_cache, 0, 0);  /* imm=1 */
      aa64_emit_orr(reg_temp, reg_temp, reg_z_cache);
      ret = this->emit_ptr;
      aa64_emit_cbz(reg_temp, 0);
      break;
    case CondGE:
      aa64_emit_sub<NoFlags>(reg_temp, reg_n_cache, reg_v_cache);
      ret = this->emit_ptr;
      aa64_emit_cbnz(reg_temp, 0);
      break;
    case CondLT:
      aa64_emit_sub<NoFlags>(reg_temp, reg_n_cache, reg_v_cache);
      ret = this->emit_ptr;
      aa64_emit_cbz(reg_temp, 0);
      break;
    case CondGT:
      aa64_emit_xor(reg_temp, reg_n_cache, reg_v_cache);
      aa64_emit_orr(reg_temp, reg_temp, reg_z_cache);
      ret = this->emit_ptr;
      aa64_emit_cbnz(reg_temp, 0);
      break;
    case CondLE:
      aa64_emit_xor(reg_temp, reg_n_cache, reg_v_cache);
      aa64_emit_orr(reg_temp, reg_temp, reg_z_cache);
      ret = this->emit_ptr;
      aa64_emit_cbz(reg_temp, 0);
      break;
    };

    return ret;
  }

  // ======== Thumb instructions ======================================
  template <ARMOp aluop>
  inline void thumb_aluop3(const ThumbInst & it) {
    const arm64_regnum rs = arm_to_a64_reg[it.rs()];
    const arm64_regnum rn = arm_to_a64_reg[it.rn()];
    const arm64_regnum rd = arm_to_a64_reg[it.rd()];

    switch (aluop) {
    case OpAdd:
      aa64_emit_add<SetFlags>(rd, rs, rn);
      break;
    case OpSub:
      aa64_emit_sub<SetFlags>(rd, rs, rn);
      break;
    };

    update_nzcv_arith_flags<SetFlags>(it);
  }

  template <ARMOp aluop>
  inline void thumb_aluop2(const ThumbInst & it) {
    const arm64_regnum rs = arm_to_a64_reg[it.rs()];
    const arm64_regnum rd = arm_to_a64_reg[it.rd()];

    switch (aluop) {
    case OpOrr:
      aa64_emit_orr(rd, rd, rs);
      update_nz_flags<SetFlags>(it, rd);
      break;
    case OpAnd:
      aa64_emit_and(rd, rd, rs);
      update_nz_flags<SetFlags>(it, rd);
      break;
    case OpXor:
      aa64_emit_xor(rd, rd, rs);
      update_nz_flags<SetFlags>(it, rd);
      break;
    case OpBic:
      aa64_emit_bic(rd, rd, rs);
      update_nz_flags<SetFlags>(it, rd);
      break;
    case OpMul:
      aa64_emit_mul(rd, rd, rs);
      update_nz_flags<SetFlags>(it, rd);
      break;
    case OpAdd:
      aa64_emit_add<SetFlags>(rd, rd, rs);
      update_nzcv_arith_flags<SetFlags>(it);
      break;
    case OpSub:
      aa64_emit_sub<SetFlags>(rd, rd, rs);
      update_nzcv_arith_flags<SetFlags>(it);
      break;
    case OpAdc:
      load_c_flag();
      aa64_emit_adc<SetFlags>(rd, rd, rs);
      update_nzcv_arith_flags<SetFlags>(it);
      break;
    case OpSbc:
      load_c_flag();
      aa64_emit_sbc<SetFlags>(rd, rd, rs);
      update_nzcv_arith_flags<SetFlags>(it);
      break;
    };
  }

  template <OpType stype, ShiftType st>
  inline void thumb_shft(const ThumbInst & it) {
    const arm64_regnum rd = arm_to_a64_reg[it.rd()];

    if (stype == OpImm) {
      if (it.gen_flag_c())
        emit_op2_shimm<SetFlags>(rd, it.rs(), st, it.imm5(), 0);
      else
        emit_op2_shimm<NoFlags>(rd, it.rs(), st, it.imm5(), 0);
    } else {
      if (it.gen_flag_c())
        emit_op2_shreg<SetFlags>(rd, it.rd(), it.rs(), st, 0);
      else
        emit_op2_shreg<NoFlags>(rd, it.rd(), it.rs(), st, 0);
    }

    update_nz_flags<SetFlags>(it, rd);
  }

  template <ARMOp aluop>
  inline void thumb_aluop1(const ThumbInst & it) {
    const arm64_regnum rs = arm_to_a64_reg[it.rs()];
    const arm64_regnum rd = arm_to_a64_reg[it.rd()];

    switch (aluop) {
    case OpNeg:
      aa64_emit_sub<SetFlags>(rd, reg_zero, rs);
      update_nzcv_arith_flags<SetFlags>(it);
      break;
    case OpMvn:
      aa64_emit_orn(rd, reg_zero, rs);
      update_nz_flags<SetFlags>(it, rd);
      break;
    };
  }

  template <ARMOp testop>
  inline void thumb_testop(const ThumbInst & it) {
    const arm64_regnum rs = arm_to_a64_reg[it.rs()];
    const arm64_regnum rd = arm_to_a64_reg[it.rd()];

    switch (testop) {
    case OpTst:
      aa64_emit_and(reg_temp, rd, rs);
      update_nz_flags<SetFlags>(it, reg_temp);
      break;
    case OpCmp:
      aa64_emit_sub<SetFlags>(reg_zero, rd, rs);
      update_nzcv_arith_flags<SetFlags>(it);
      break;
    case OpCmn:
      aa64_emit_add<SetFlags>(reg_zero, rd, rs);
      update_nzcv_arith_flags<SetFlags>(it);
      break;
    };
  }

  template <ARMOp aluop>
  inline void thumb_aluimm2(const ThumbInst & it) {
    const arm64_regnum rd = arm_to_a64_reg[it.rd8()];

    switch (aluop) {
    case OpMov:
      aa64_emit_movlo(rd, it.imm8());
      aa64_emit_movlo(reg_n_cache, 0);
      aa64_emit_movlo(reg_z_cache, it.imm8() ? 0 : 1);
      break;
    case OpAdd:
      aa64_emit_addi<SetFlags>(rd, rd, it.imm8());
      update_nzcv_arith_flags<SetFlags>(it);
      break;
    case OpSub:
      aa64_emit_subi<SetFlags>(rd, rd, it.imm8());
      update_nzcv_arith_flags<SetFlags>(it);
      break;
    case OpCmp:
      aa64_emit_subi<SetFlags>(reg_temp, rd, it.imm8());
      update_nzcv_arith_flags<SetFlags>(it);
      break;
    };
  }

  template <ARMOp aluop>
  inline void thumb_aluimm3(const ThumbInst & it) {
    const arm64_regnum rs = arm_to_a64_reg[it.rs()];
    const arm64_regnum rd = arm_to_a64_reg[it.rd()];

    switch (aluop) {
    case OpAdd:
      aa64_emit_addi<SetFlags>(rd, rs, it.imm3());
      break;
    case OpSub:
      aa64_emit_subi<SetFlags>(rd, rs, it.imm3());
      break;
    };

    update_nzcv_arith_flags<SetFlags>(it);
  }

  template <ARMOp aluop>
  inline void thumb_aluhi(const ThumbInst & it, u32 & cycle_count) {
    const arm64_regnum rs = load_alloc_reg(it.rs_hi(), reg_a1, it.pc + 4);

    // TODO: Improve PC writes (reg_a0 *must* contain the new PC, which is not clear).
    if (aluop == OpAdd) {
      const arm64_regnum rd = load_alloc_reg(it.rd_hi(), reg_a0, it.pc + 4);
      aa64_emit_add<NoFlags>(rd, rd, rs);
      check_store_reg_pc_thumb(it.rd_hi());
    } else if (aluop == OpCmp) {
      const arm64_regnum rd = load_alloc_reg(it.rd_hi(), reg_a0, it.pc + 4);
      aa64_emit_sub<SetFlags>(reg_temp, rd, rs);
      update_nzcv_arith_flags<SetFlags>(it);
    } else if (aluop == OpMov) {
      const arm64_regnum rd = store_alloc_reg(it.rd_hi(), reg_a0);
      aa64_emit_mov(rd, rs);
      check_store_reg_pc_thumb(it.rd_hi());
    }
  }

  template <u32 ref_reg>
  inline void thumb_regoff(const ThumbInst & it) {
    if (ref_reg == REG_PC)
      generate_load_pc(arm_to_a64_reg[it.rd8()], (it.pc & ~2) + 4 + 4 * it.imm8());
    else
      aa64_emit_addi<NoFlags>(arm_to_a64_reg[it.rd8()], arm_to_a64_reg[ref_reg], 4 * it.imm8());
  }

  inline void thumb_spadj(s8 offset) {
    if (offset >= 0)
      aa64_emit_addi<NoFlags>(reg_r13, reg_r13,  offset * 4);
    else
      aa64_emit_subi<NoFlags>(reg_r13, reg_r13, -offset * 4);
  }

  inline void thumb_bx(u32 pc, u32 regn, u32 & cycle_count) {
    force_load_reg(regn, reg_a0, pc + 4);
    generate_indirect_branch_cycle_update(dual);
  }

  inline void arm_bx(const ARMInst & it, u32 & cycle_count) {
    const u8 condition = it.cond();        // TODO remove this
    force_load_reg(it.rm(), reg_a0, it.pc + 8);
    generate_indirect_branch_dual();
  }

  inline bool thumb_emu_swi(u32 pc, u32 num, u32 & cycle_count) {
    switch (num) {
    case 6:
    case 7:
      {
        const arm64_regnum regA = (num == 6) ? reg_r0 : reg_r1;
        const arm64_regnum regB = (num == 6) ? reg_r1 : reg_r0;

        aa64_emit_sdiv(reg_r3, regA, regB);
        aa64_emit_msub(reg_r1, regA, regB, reg_r3);
        aa64_emit_mov(reg_r0, reg_r3);
        aa64_emit_cmpi(reg_r3, 0);
        aa64_emit_csneg(reg_r3, reg_r3, reg_r3, ccode_ge);
      }
      cycle_count += 64;    // Big under-estimation here
      return true;
    default:
      return false;
    };
    return false;
  }

  inline bool arm_emu_swi(u32 pc, u32 num, u32 & cycle_count) {
    return thumb_emu_swi(pc, num, cycle_count);
  }

  inline u8* thumb_swi(u32 pc, u32 & cycle_count) {
    u8 *brtgt = NULL;
    generate_load_pc(reg_a0, (pc + 2));
    generate_function_call(execute_swi);
    generate_branch_cycle_update(brtgt, 0x00000008);
    return brtgt;
  }

  inline u8* arm_swi(u32 pc, u32 & cycle_count) {
    u8 *brtgt = NULL;
    generate_load_pc(reg_a0, (pc + 4));
    generate_function_call(execute_swi);
    generate_branch_cycle_update(brtgt, 0x00000008);
    return brtgt;
  }

  template <ARMCondCode ccode>
  inline u8* thumb_brcond(u32 pc, u32 target, u32 & cycle_count) {
    u8 *brtgt = NULL;

    generate_cycle_update(cycle_count);
    u8 *ptch = emit_opp_condbranch(ccode);
    generate_branch_no_cycle_update(brtgt, target);
    generate_branch_patch_conditional(ptch, this->emit_ptr);
    return brtgt;
  }

  inline u8* thumb_b(u32 pc, u32 target, u32 & cycle_count) {
    u8 *brtgt = NULL;
    generate_branch_cycle_update(brtgt, target);
    return brtgt;
  }

  inline u8* arm_b(const ARMInst & it, u32 target, u32 & cycle_count) {
    const u32 pc = it.pc;  // TODO: Remove this
    u8 *brtgt = NULL;
    if (it.cond() == CondAL) {
      generate_branch_cycle_update(brtgt, target);
    } else {
      generate_branch_no_cycle_update(brtgt, target);
    }
    return brtgt;
  }

  inline u8* thumb_bl(u32 pc, u32 target, u32 & cycle_count) {
    u8 *brtgt = NULL;

    generate_load_pc(reg_r14, ((pc + 2) | 0x01));
    generate_branch_cycle_update(brtgt, target);
    return brtgt;
  }

  inline u8* arm_bl(const ARMInst & it, u32 target, u32 & cycle_count) {
    const u32 pc = it.pc;  // TODO: Remove this
    u8 *brtgt = NULL;
    generate_load_pc(reg_r14, ((pc + 4)));
    if (it.cond() == CondAL) {
      generate_branch_cycle_update(brtgt, target);
    } else {
      generate_branch_no_cycle_update(brtgt, target);
    }
    return brtgt;
  }

  inline void thumb_blh(u32 pc, u32 offset, u32 & cycle_count) {
    aa64_emit_addlimm<NoFlags>(reg_a0, reg_r14, offset);
    generate_load_pc(reg_r14, ((pc + 2) | 0x01));
    generate_indirect_branch_cycle_update(thumb);
  }


  // ============= Memory functions =================
  template <typename memtype, ThumbMemOffset offt>
  inline void thumb_memaddr(const ThumbInst & it, u32 regn) {
    // Generate the memory address to a0
    switch (offt) {
    case OffPC:
      // PC-relative offset. It is word aligned.
      generate_load_pc(reg_a0, ((it.pc & (~3U)) + it.imm8() * 4 + 4));
      break;

    // rb/ro/regn are never PC in thumb mode (this is handled by OffPC mode)
    case OffReg:
      aa64_emit_add<NoFlags>(reg_a0, arm_to_a64_reg[regn], arm_to_a64_reg[it.ro()]);
      break;
    case OffImm5:
      aa64_emit_addi<NoFlags>(reg_a0, arm_to_a64_reg[regn], it.imm5() * sizeof(memtype));
      break;
    case OffImm8:
      aa64_emit_addi<NoFlags>(reg_a0, arm_to_a64_reg[regn], it.imm8() * sizeof(memtype));
      break;
    }
  }

  template <typename memtype, ThumbMemOffset offt>
  inline void thumb_memld(const ThumbInst & it, u32 regd, u32 regn, u32 & cycle_count) {
    cycle_count += 2;  // TODO: Use proper cycle accounting and honor WAITCNT

    // Generate the address
    thumb_memaddr<memtype, offt>(it, regn);
    // Generate a call to the right memory section handler.
    generate_load_pc(reg_a1, it.pc);
    generate_function_call(call_ldr_handler<memtype>());
    generate_store_reg(reg_res, regd);
  }

  template <typename memtype, ThumbMemOffset offt>
  inline void thumb_memst(const ThumbInst & it, u32 regd, u32 regn, u32 & cycle_count) {
    cycle_count++;  // TODO: Use proper cycle accounting and honor WAITCNT

    // Generate the address
    thumb_memaddr<memtype, offt>(it, regn);
    // Load value and generate call to handler
    force_load_reg(regd, reg_a1, it.pc + 4);
    generate_load_pc(reg_a2, (it.pc + 2));
    generate_function_call(call_str_handler<memtype>());
  }

  template <ARMMemOffset offt, MemOffDir dir>
  inline void arm_memaddr(arm64_regnum oreg, const ARMInst & it) {
    // Load base register if needed
    const arm64_regnum breg = load_alloc_reg(it.rn(), oreg, it.pc + 8);

    switch (offt) {
    case OffImm12:     // [rn +/- imm12]
      if (dir == OffPositive)
        aa64_emit_addi<NoFlags>(oreg, breg, it.off12());
      else
        aa64_emit_subi<NoFlags>(oreg, breg, it.off12());
      break;
    case OffHImm8:     // [rn +/- imm8]
      if (dir == OffPositive)
        aa64_emit_addi<NoFlags>(oreg, breg, it.off8());
      else
        aa64_emit_subi<NoFlags>(oreg, breg, it.off8());
      break;
    case OffHReg:      // [rn +/- rm]
      {
        const arm64_regnum secreg = load_alloc_reg(it.rm(), reg_temp, it.pc + 8);
        if (dir == OffPositive)
          aa64_emit_add<NoFlags>(oreg, breg, secreg);
        else
          aa64_emit_sub<NoFlags>(oreg, breg, secreg);
      }
      break;
    case OffOp2Reg:    // [rn +/- rm shift/rot amount]
      emit_op2_shimm<NoFlags>(reg_a2, it.rm(), (ShiftType)it.op2smode(), it.op2sa(), it.pc + 8);
      if (dir == OffPositive)
        aa64_emit_add<NoFlags>(oreg, breg, reg_a2);
      else
        aa64_emit_sub<NoFlags>(oreg, breg, reg_a2);
      break;
    };
  }

  template <typename memtype, ARMMemOffset offt, MemOffDir dir, MemIdxMode idxm>
  inline void arm_memst(const ARMInst & it, u32 & cycle_count) {
    cycle_count++;    // TODO: Use proper cycle accounting and honor WAITCNT

    // Generate the final address and base address, and write back if necessary
    if (idxm == MemIdxPostWB) {
      // Load the base reg to a0
      force_load_reg(it.rn(), reg_a0, it.pc + 4);
      // Calculate the final value to the final reg.
      const arm64_regnum wbreg = store_alloc_reg(it.rn(), reg_a2);
      arm_memaddr<offt, dir>(wbreg, it);
    }
    else {
      arm_memaddr<offt, dir>(reg_a0, it);  // Calculate final addr to a0
      if (idxm == MemIdxPreWB) {
        generate_store_reg(reg_a0, it.rn());
      }
    }

    // Generate call to handler, load the value to write to a1
    force_load_reg(it.rd(), reg_a1, it.pc + 12);
    generate_load_pc(reg_a2, (it.pc + 4));
    generate_function_call(call_str_handler<memtype>());
  }

  template <typename memtype, ARMMemOffset offt, MemOffDir dir, MemIdxMode idxm>
  inline void arm_memld(const ARMInst & it, u32 & cycle_count) {
    const u8 condition = it.cond();        // TODO remove this
    cycle_count += 2;    // TODO: Use proper cycle accounting and honor WAITCNT

    // Generate the final address and base address, and write back if necessary
    if (idxm == MemIdxPostWB) {
      // Load the base reg to a0
      force_load_reg(it.rn(), reg_a0, it.pc + 4);
      // Calculate the final value to the final reg.
      const arm64_regnum wbreg = store_alloc_reg(it.rn(), reg_a2);
      arm_memaddr<offt, dir>(wbreg, it);
    }
    else {
      arm_memaddr<offt, dir>(reg_a0, it);  // Calculate final addr to a0
      if (idxm == MemIdxPreWB) {
        generate_store_reg(reg_a0, it.rn());
      }
    }

    // Generate call to handler, load the value to write to a1
    generate_load_pc(reg_a1, it.pc);
    generate_function_call(call_ldr_handler<memtype>());
    generate_store_reg(reg_res, it.rd());

    check_store_reg_pc_no_flags(it.rd());
  }

  template <typename memtype>
  inline void arm_swap(const ARMInst & it, u32 & cycle_count) {
    cycle_count += 3;   // TODO: Some more accurate accounting :)

    // rd = mem[rn], mem[rn] = rm (Note: all regs could be the same!)

    force_load_reg(it.rn(), reg_a0, it.pc + 4);
    generate_load_pc(reg_a1, it.pc);
    generate_function_call(call_ldr_handler<memtype>());

    aa64_emit_mov(reg_temp, reg_res);
    force_load_reg(it.rn(), reg_a0, it.pc + 4);
    force_load_reg(it.rm(), reg_a1, it.pc + 4);
    generate_store_reg(reg_temp, it.rd());
    generate_load_pc(reg_a2, (it.pc + 4));
    generate_function_call(call_str_handler<memtype>());
  }

  template <CPUInstMode cpum, AccMode amode, AddrMode addrmode, bool writeback, bool sbit>
  inline void mem_multi(u32 pc, u32 condition, u32 basereg, u16 rlist, u32 & cycle_count) {
    const u32 numops = bit_count[rlist >> 8] + bit_count[rlist & 0xFF];
    cycle_count += numops;    // TODO: Use proper cycle accounting.

    const u32 itsize = (cpum == ModeARM) ? 4 : 2;
    const s32 stpoff = (addrmode == AddrPreInc || addrmode == AddrPostInc) ? 4 : -4;
    const s32 endoff = stpoff * numops;
    const s32 inioff = (addrmode == AddrPreInc)  ? 4 :
                       (addrmode == AddrPostInc) ? 0 :
                       (addrmode == AddrPreDec)  ? endoff :
                                                   endoff + 4;

    // Load base register, clearing the lowest 2 bits (align)
    const arm64_regnum screg = load_alloc_reg(basereg, reg_save0, pc + 2*itsize);
    aa64_emit_andi(reg_save0, screg, 30, 29);  /* clear 2 LSB */

    // If base is in the reglist and writeback is enabled, the value of the
    // written register depends on the write cycle (ARM7TDM manual 4.11.6).
    // If the register is the first, the written value is the original value,
    // otherwise the update base register is written. For LDM loaded data
    // takes always precendence.
    bool wrbck_base = (1 << basereg) & rlist;
    bool base_first = (((1 << basereg) - 1) & rlist) == 0;
    bool writeback_first = (amode == AccLoad) || !(wrbck_base && base_first);

    // This is the most common case by far.
    if (writeback && writeback_first)
      aa64_emit_addsubi(arm_to_a64_reg[basereg], arm_to_a64_reg[basereg], endoff);

    u32 aoff = 0;
    for (u32 i = 0; i < 16; i++) {
      if (rlist & (1 << i)) {
        aa64_emit_addsubi(reg_a0, reg_save0, aoff + inioff);
        if (amode == AccLoad) {
          generate_function_call(execute_aligned_load32);
          generate_store_reg(reg_res, i);
        } else {
          force_load_reg(i, reg_a1, pc + 2*itsize);

          // Update the base register right after the first read if necessary
          if (writeback && !writeback_first) {
            aa64_emit_addsubi(arm_to_a64_reg[basereg], arm_to_a64_reg[basereg], endoff);
            writeback_first = true;
          }

          if (rlist >> (i + 1)) {
            generate_function_call(execute_aligned_store32);
          } else {
            // Only the last store can produce side-effects
            // TODO: Evaluate if this is enough or we should improve it.
            generate_load_pc(reg_a2, (pc + itsize));
            generate_function_call(execute_store_u32);
          }
        }
        aoff += 4;
      }
    }

    // Load PC requires an indirect branch
    if (amode == AccLoad && (rlist & (1 << REG_PC))) {
      if (cpum == ModeARM) {
        generate_indirect_branch_arm();
      } else {
        generate_indirect_branch_cycle_update(thumb);
      }
    }
  }


  // ======== ARM instructions ======================================
  template <ARMOp aluop, FlagOperation flg>
  inline void arm_aluimm3(const ARMInst & it, u32 & cycle_count) {
    const arm64_regnum rn = load_alloc_reg(it.rn(), reg_a1, it.pc + 8);
    const arm64_regnum rd = store_alloc_reg(it.rd(), reg_a0);

    // Immediate is a 8 bit rotated immediate
    const u32 sa = it.rot4() * 2;   // TODO remove this absurd scaling here
    const u32 imm = rotr32(it.imm8(), sa);

    // Set/Clear carry flag if appropriate (rotation result)
    if (aluop == OpAnd || aluop == OpOrr || aluop == OpXor || aluop == OpBic) {
      if (flg == SetFlags && it.rot4() != 0 && it.gen_flag_c())
        aa64_emit_movlo(reg_c_cache, ((imm) >> 31));
    }

    // TODO: Implement arm64 immediates for logic operations.
    // Should be easy for 8 bit rotated immediates.
    switch (aluop) {
    case OpAnd:
      generate_load_imm(reg_temp, imm);
      aa64_emit_and(rd, rn, reg_temp);
      update_nz_flags<flg>(it, rd);
      break;
    case OpOrr:
      generate_load_imm(reg_temp, imm);
      aa64_emit_orr(rd, rn, reg_temp);
      update_nz_flags<flg>(it, rd);
      break;
    case OpXor:
      generate_load_imm(reg_temp, imm);
      aa64_emit_xor(rd, rn, reg_temp);
      update_nz_flags<flg>(it, rd);
      break;
    case OpBic:
      generate_load_imm(reg_temp, imm);
      aa64_emit_bic(rd, rn, reg_temp);
      update_nz_flags<flg>(it, rd);
      break;
    case OpAdd:
     aa64_emit_addlimm<flg>(rd, rn, imm);
      if (flg == SetFlags)
        update_nzcv_arith_flags<SetFlags>(it);
      break;
    case OpAdc:
      load_c_flag();
      generate_load_imm(reg_temp, imm);
      aa64_emit_adc<flg>(rd, rn, reg_temp);
      update_nzcv_arith_flags<flg>(it);
      break;
    case OpSub:
      aa64_emit_sublimm<flg>(rd, rn, imm);
      if (flg == SetFlags)
        update_nzcv_arith_flags<SetFlags>(it);
      break;
    case OpRsb:
      generate_load_imm(reg_temp, imm);
      aa64_emit_sub<flg>(rd, reg_temp, rn);
      update_nzcv_arith_flags<flg>(it);
      break;
    case OpSbc:
      load_c_flag();
      generate_load_imm(reg_temp, imm);
      aa64_emit_sbc<flg>(rd, rn, reg_temp);
      update_nzcv_arith_flags<flg>(it);
      break;
    case OpRsc:
      load_c_flag();
      generate_load_imm(reg_temp, imm);
      aa64_emit_sbc<flg>(rd, reg_temp, rn);
      update_nzcv_arith_flags<flg>(it);
      break;
    };

    const u8 condition = it.cond();        // TODO remove this
    if (flg == NoFlags) {
      check_store_reg_pc_no_flags(it.rd());
    } else {
      check_store_reg_pc_flags(it.rd());
    }
  }

  template <ARMOp aluop>
  inline void arm_aluimm2(const ARMInst & it, u32 & cycle_count) {
    const arm64_regnum rn = load_alloc_reg(it.rn(), reg_a1, it.pc + 8);

    // Immediate is a 8 bit rotated immediate
    const u32 imm = rotr32(it.imm8(), it.rot4() * 2);

    // Set/Clear carry flag if appropriate (rotation result)
    if (it.rot4() != 0 && it.gen_flag_c())
      aa64_emit_movlo(reg_c_cache, ((imm) >> 31));

    switch (aluop) {
    case OpTst:
      generate_load_imm(reg_temp, imm);
      aa64_emit_and(reg_temp, rn, reg_temp);
      update_nz_flags<SetFlags>(it, reg_temp);
      break;
    case OpTeq:
      generate_load_imm(reg_temp, imm);
      aa64_emit_xor(reg_temp, rn, reg_temp);
      update_nz_flags<SetFlags>(it, reg_temp);
      break;
    case OpCmp:
      aa64_emit_sublimm<SetFlags>(reg_temp, rn, imm);
      update_nzcv_arith_flags<SetFlags>(it);
      break;
    case OpCmn:
      aa64_emit_addlimm<SetFlags>(reg_temp, rn, imm);
      update_nzcv_arith_flags<SetFlags>(it);
      break;
    };
  }

  template <ARMOp aluop, FlagOperation flg>
  inline void arm_aluimm1(const ARMInst & it, u32 & cycle_count) {
    const arm64_regnum rd = store_alloc_reg(it.rd(), reg_a0);

    // Immediate is a 8 bit rotated immediate
    u32 imm = rotr32(it.imm8(), it.rot4() * 2);

    // Set/Clear carry flag if appropriate (rotation result)
    if (flg == SetFlags && it.rot4() != 0 && it.gen_flag_c())
      aa64_emit_movlo(reg_c_cache, ((imm) >> 31));

    if (aluop == OpMvn)
      imm = ~imm;

    generate_load_imm(rd, imm);
    upd_nz_flags_imm<flg>(it, imm);

    const u8 condition = it.cond();        // TODO remove this
    if (flg == NoFlags) {
      check_store_reg_pc_no_flags(it.rd());
    } else {
      check_store_reg_pc_flags(it.rd());
    }
  }

  // Calculates operand 2 when register is shifted/rotated by an immediate.
  template<FlagOperation flg>
  inline void emit_op2_shimm(arm64_regnum dreg, u32 sreg, ShiftType st, u32 sa, u32 pc) {
    arm64_regnum rm;

    switch (st) {
    case ShiftLSL:
      rm = load_alloc_reg(sreg, dreg, pc);
      if (flg == SetFlags && sa)
        aa64_emit_ubfx(reg_c_cache, rm, (32 - sa), 1);
      aa64_emit_lsl(dreg, rm, sa);
      break;

    case ShiftLSR:      /* (sa 0 means shift by 32) */
      if (sa) {
        rm = load_alloc_reg(sreg, dreg, pc);
        if (flg == SetFlags)
          aa64_emit_ubfx(reg_c_cache, rm, (sa - 1), 1);
        aa64_emit_lsr(dreg, rm, sa);
      } else {
        if (flg == SetFlags) {
          rm = load_alloc_reg(sreg, dreg, pc);
          aa64_emit_lsr(reg_c_cache, rm, 31);
        }
        aa64_emit_movlo(dreg, 0);
      }
      break;

    case ShiftASR:      /* (sa 0 is also shift by 32) */
      rm = load_alloc_reg(sreg, dreg, pc);
      if (flg == SetFlags)
        aa64_emit_ubfx(reg_c_cache, rm, ((sa ? sa : 32) - 1), 1);
      aa64_emit_asr(dreg, rm, (sa ? sa : 31));
      break;

    case ShiftROR:
      rm = load_alloc_reg(sreg, reg_temp, pc);
      if (sa) {
        if (flg == SetFlags)
          aa64_emit_ubfx(reg_c_cache, rm, (sa - 1), 1);
        aa64_emit_ror(dreg, rm, sa);
      } else {
        // TODO this doesn't work when rm and dreg are the same register.
        aa64_emit_extr(dreg, reg_c_cache, rm, 1);
        if (flg == SetFlags)
          aa64_emit_ubfx(reg_c_cache, rm, 0, 1);
      }
      break;
    };
  }

  // Calculates operand 2 when register is shifted/rotated by another register.
  template<FlagOperation flg>
  inline void emit_op2_shreg(arm64_regnum dreg, u32 sreg, u32 areg, ShiftType st, u32 pc) {
    load_alloc_reg_lsb(areg, reg_a1, pc);  // Loads the LSB byte only!

    if (flg == SetFlags) {
      force_load_reg(sreg, dreg, pc);    // Force load reg into dreg
      switch (st) {
        case 0:     /* LSL */
          aa64_emit_cbz(reg_a1, 8);           // Skip it all on shift = 0
          // This code works if shift <= 32.
          aa64_emit_subi<NoFlags>(reg_temp, reg_a1, 1);
          aa64_emit_lslv(dreg, dreg, reg_temp);
          aa64_emit_lsr(reg_c_cache, dreg, 31);
          aa64_emit_cmpi(reg_a1, 33);
          aa64_emit_lsl(dreg, dreg, 1);
          // If shift > 32 we just clear both reg and C flag
          aa64_emit_csel(reg_c_cache, reg_zero, reg_c_cache, ccode_hs);
          aa64_emit_csel(dreg,        reg_zero, dreg,        ccode_hs);
          break;
        case 1:     /* LSR */
          aa64_emit_cbz(reg_a1, 8);           // Skip it all on shift = 0
          aa64_emit_subi<NoFlags>(reg_temp, reg_a1, 1);
          aa64_emit_lsrv(dreg, dreg, reg_temp);
          aa64_emit_andi(reg_c_cache, dreg, 0, 0);  /* imm=1 */
          aa64_emit_cmpi(reg_a1, 33);
          aa64_emit_lsr(dreg, dreg, 1);
          // If shift > 32 we just clear both reg and C flag
          aa64_emit_csel(reg_c_cache, reg_zero, reg_c_cache, ccode_hs);
          aa64_emit_csel(dreg,        reg_zero, dreg,        ccode_hs);
          break;
        case 2:     /* ASR */
          aa64_emit_cbz(reg_a1, 8);           // Skip it all on shift = 0
          aa64_emit_movlo(reg_temp, 32);      // Cap amount to 32.
          aa64_emit_cmpi(reg_a1, 32);
          aa64_emit_csel(reg_a1, reg_a1, reg_temp, ccode_ls);
          aa64_emit_subi<NoFlags>(reg_temp, reg_a1, 1);
          aa64_emit_asrv(dreg, dreg, reg_temp);
          aa64_emit_andi(reg_c_cache, dreg, 0, 0);  /* imm=1 */
          aa64_emit_asr(dreg, dreg, 1);
          break;
        case 3:     /* ROR */
          // ror/lsrv only use the 5 LSB in aarch64
          aa64_emit_rorv(dreg, dreg, reg_a1);
          aa64_emit_cbz(reg_a1, 2);
          aa64_emit_lsr(reg_c_cache, dreg, 31);
          break;
      };
    } else {
      const arm64_regnum rm = load_alloc_reg(sreg, dreg, pc);
      switch (st) {
        case 0:     /* LSL */
          aa64_emit_cmpi(reg_a1, 32);
          aa64_emit_lslv(reg_temp, rm, reg_a1);
          aa64_emit_csel(dreg, reg_zero, reg_temp, ccode_hs);
          break;
        case 1:     /* LSR */
          aa64_emit_cmpi(reg_a1, 32);
          aa64_emit_lsrv(reg_temp, rm, reg_a1);
          aa64_emit_csel(dreg, reg_zero, reg_temp, ccode_hs);
          break;
        case 2:     /* ASR */
          aa64_emit_cmpi(reg_a1, 31);
          aa64_emit_asr(reg_temp, rm, 31);
          aa64_emit_asrv(dreg, rm, reg_a1);
          aa64_emit_csel(dreg, dreg, reg_temp, ccode_lo);
          break;
        case 3:     /* ROR */
          aa64_emit_rorv(dreg, rm, reg_a1);
          break;
      };
    }
  }

  // Calculates the flex operand, honoring flag (CF) generation and returns the
  // native register where the value is placed (either reg_a0 or some ARM reg).
  template <FlagOperation flg>
  inline arm64_regnum emit_arm_aluop2(const ARMInst & it) {
    // Calculates the Op2 part and writes it to a0
    if (it.op2imm()) {
      // Special case: LSL with imm = 0 means unmodified register (and Cflag).
      // Just return the register directly (or scratch to a0 for PC)
      // Saves one instruction (it is relatively common)
      if (it.op2sa() == 0 && it.op2smode() == 0 /* LSL */)
        return load_alloc_reg(it.rm(), reg_a0, it.pc + 8);

      if (flg == SetFlags && it.gen_flag_c())
        emit_op2_shimm<SetFlags>(reg_a0, it.rm(), (ShiftType)it.op2smode(), it.op2sa(), it.pc + 8);
      else
        emit_op2_shimm<NoFlags>(reg_a0, it.rm(), (ShiftType)it.op2smode(), it.op2sa(), it.pc + 8);
    } else {
      if (flg == SetFlags && it.gen_flag_c())
        emit_op2_shreg<SetFlags>(reg_a0, it.rm(), it.rs(), (ShiftType)it.op2smode(), it.pc + 12);
      else
        emit_op2_shreg<NoFlags>(reg_a0, it.rm(), it.rs(), (ShiftType)it.op2smode(), it.pc + 12);
    }
    return reg_a0;
  }

  // 3 regs (with op2) instructions
  template <ARMOp aluop, FlagOperation flg>
  inline void arm_alureg3(const ARMInst & it, u32 & cycle_count) {
    // Generate op2 to a0, op1 to a1
    const arm64_regnum regop2 = (aluop == OpAdd || aluop == OpSub || aluop == OpRsb ||
                                 aluop == OpAdc || aluop == OpSbc || aluop == OpRsc) ?
                                 emit_arm_aluop2<NoFlags>(it) :  // Do not generate C flag
                                 emit_arm_aluop2<flg>(it);

    const arm64_regnum rn = load_alloc_reg(it.rn(), reg_a1, it.pc + (it.op2imm() ? 8 : 12));
    const arm64_regnum rd = store_alloc_reg(it.rd(), reg_a0);

    switch (aluop) {
    case OpAnd:
      aa64_emit_and(rd, rn, regop2);
      update_nz_flags<flg>(it, rd);
      break;
    case OpOrr:
      aa64_emit_orr(rd, rn, regop2);
      update_nz_flags<flg>(it, rd);
      break;
    case OpXor:
      aa64_emit_xor(rd, rn, regop2);
      update_nz_flags<flg>(it, rd);
      break;
    case OpBic:
      aa64_emit_bic(rd, rn, regop2);
      update_nz_flags<flg>(it, rd);
      break;
    case OpAdd:
      aa64_emit_add<flg>(rd, rn, regop2);
      update_nzcv_arith_flags<flg>(it);
      break;
    case OpAdc:
      load_c_flag();
      aa64_emit_adc<flg>(rd, rn, regop2);
      update_nzcv_arith_flags<flg>(it);
      break;
    case OpSub:
      aa64_emit_sub<flg>(rd, rn, regop2);
      update_nzcv_arith_flags<flg>(it);
      break;
    case OpSbc:
      load_c_flag();
      aa64_emit_sbc<flg>(rd, rn, regop2);
      update_nzcv_arith_flags<flg>(it);
      break;
    case OpRsb:
      aa64_emit_sub<flg>(rd, regop2, rn);
      update_nzcv_arith_flags<flg>(it);
      break;
    case OpRsc:
      load_c_flag();
      aa64_emit_sbc<flg>(rd, regop2, rn);
      update_nzcv_arith_flags<flg>(it);
      break;
    };

    const u8 condition = it.cond();        // TODO remove this
    if (flg == NoFlags) {
      check_store_reg_pc_no_flags(it.rd());
    } else {
      check_store_reg_pc_flags(it.rd());
    }
  }

  template <ARMOp aluop, FlagOperation flg>
  inline void arm_alureg1(const ARMInst & it, u32 & cycle_count) {
    const arm64_regnum regop2 = emit_arm_aluop2<flg>(it);   // Generate op2 to a0
    const arm64_regnum rd = store_alloc_reg(it.rd(), reg_a0);

    switch (aluop) {
    case OpMvn:
      aa64_emit_orn(rd, reg_zero, regop2);
      break;
    case OpMov:
      aa64_emit_mov(rd, regop2);
      break;
    };

    update_nz_flags<flg>(it, rd);

    const u8 condition = it.cond();        // TODO remove this
    if (flg == NoFlags) {
      check_store_reg_pc_no_flags(it.rd());
    } else {
      check_store_reg_pc_flags(it.rd());
    }
  }

  // compare/test instructions
  template <ARMOp aluop, FlagOperation c_flag>
  inline void arm_alureg2(const ARMInst & it) {
    const arm64_regnum regop2 = emit_arm_aluop2<c_flag>(it);   // Generate op2 to a0 (with/without C flag)
    const arm64_regnum rn = load_alloc_reg(it.rn(), reg_a1, it.pc + (it.op2imm() ? 8 : 12));

    switch (aluop) {
    case OpTst:
       aa64_emit_and(reg_temp, rn, regop2);
       update_nz_flags<SetFlags>(it, reg_temp);
       break;
    case OpTeq:
       aa64_emit_xor(reg_temp, rn, regop2);
       update_nz_flags<SetFlags>(it, reg_temp);
       break;
    case OpCmp:
      aa64_emit_sub<SetFlags>(reg_zero, rn, regop2);
      update_nzcv_arith_flags<SetFlags>(it);
      break;
    case OpCmn:
      aa64_emit_add<SetFlags>(reg_zero, rn, regop2);
      update_nzcv_arith_flags<SetFlags>(it);
      break;
    };
  }

  // Performs 32 bit multiplications (rd and rn are swapped)
  template<FlagOperation flg, MulMode mm>
  inline void arm_mul32(const ARMInst &it) {
    const arm64_regnum rm = load_alloc_reg(it.rm(), reg_a0, it.pc + 8);
    const arm64_regnum rs = load_alloc_reg(it.rs(), reg_a1, it.pc + 8);
    const arm64_regnum rd = store_alloc_reg(it.rn(), reg_a2);

    if (mm == MulAdd) {
      const arm64_regnum rn = load_alloc_reg(it.rd(), reg_temp, it.pc + 8);
      aa64_emit_madd(rd, rn, rm, rs);
    }
    else
      aa64_emit_mul(rd, rm, rs);

    update_nz_flags<flg>(it, rd);
    // Writing PC is not really defined.
  }

  // Performs 64 bit multiplications
  template<FlagOperation flg, MulMode mm, bool signmul>
  inline void arm_mul64(const ARMInst &it) {
    const arm64_regnum rm = load_alloc_reg(it.rm(), reg_a0, it.pc + 8);
    const arm64_regnum rs = load_alloc_reg(it.rs(), reg_a1, it.pc + 8);
    const arm64_regnum rdlo = (mm == MulAdd) ? load_alloc_reg(it.rdlo(), reg_temp, it.pc + 8)
                                             : store_alloc_reg(it.rdlo(), reg_temp);
    const arm64_regnum rdhi = (mm == MulAdd) ? load_alloc_reg(it.rdhi(), reg_temp2, it.pc + 8)
                                             : store_alloc_reg(it.rdhi(), reg_temp2);

    if (mm == MulAdd) {
      aa64_emit_merge_regs(reg_a2, rdhi, rdlo);
      if (signmul)
        aa64_emit_smaddl(reg_a2, reg_a2, rm, rs);
      else
        aa64_emit_umaddl(reg_a2, reg_a2, rm, rs);
    } else {
      if (signmul)
        aa64_emit_smaddl(reg_a2, reg_zero, rm, rs);
      else
        aa64_emit_umaddl(reg_a2, reg_zero, rm, rs);
    }

    aa64_emit_andi64(rdlo, reg_a2, 0, 31);
    aa64_emit_lsr64(rdhi, reg_a2, 32);

    if (flg == SetFlags) {
      aa64_emit_orr(reg_z_cache, rdlo, rdhi);
      aa64_emit_cmpi(reg_z_cache, 0);  // TODO: perform the check on 64 bits to save 1 inst.
      aa64_emit_cset(reg_z_cache, ccode_eq);
      aa64_emit_lsr(reg_n_cache, rdhi, 31);
    }
  }

  // PSR register read
  template<PSReg reg>
  inline void arm_read_psr(const ARMInst &it) {
    if (reg == RegCPSR) {
      generate_function_call(execute_read_cpsr);
    } else {
      generate_function_call(execute_read_spsr);
    }

    generate_store_reg(reg_res, it.rd());
  }

  // PSR register write
  template<PSReg reg, OpType opt>
  inline void arm_write_psr(const ARMInst &it) {
    if (opt == OpReg)
      force_load_reg(it.rm(), reg_a0, it.pc + 8);
    else
      generate_load_imm(reg_a0, rotr32(it.imm8(), it.rot4() * 2));

    if (reg == RegCPSR) {
      generate_load_pc(reg_a1, it.pc);
      generate_load_imm(reg_a2, cpsr_masks[it.field_fc()][0]);
      generate_load_imm(reg_temp, cpsr_masks[it.field_fc()][1]);
      generate_function_call(execute_store_cpsr);
    } else {
      generate_load_imm(reg_a1, spsr_masks[it.field_fc()]);
      generate_function_call(execute_store_spsr);
    }
  }

  template <CPUInstMode cm>
  void trace_instruction(u32 pc, u32 opcode) {
    #ifdef TRACE_INSTRUCTIONS
    for (unsigned i = 0; i < 15; i++)
      aa64_emit_str(arm_to_a64_reg[i], reg_base, i);
    generate_load_imm(reg_a0, pc);
    generate_load_imm(reg_a1, opcode);
    if (cm == ModeThumb) {
      generate_function_call(trace_instruction_hook_thumb);
    } else {
      generate_function_call(trace_instruction_hook_arm);
    }
    for (unsigned i = 0; i < 15; i++)
      aa64_emit_ldr(arm_to_a64_reg[i], reg_base, i);
    #endif
  }

};

extern void* ldst_handler_functions[16*4 + 17*6];
extern void* ldst_lookup_tables[16*4 + 17*6];

void init_emitter(bool must_swap) {
  rom_cache_watermark = INITIAL_ROM_WATERMARK;
  init_bios_hooks();

  // Generate handler table
  memcpy(ldst_lookup_tables, ldst_handler_functions, sizeof(ldst_lookup_tables));
}

u32 execute_arm_translate(u32 cycles) {
  return execute_arm_translate_internal(cycles, &reg[0]);
}

#endif

