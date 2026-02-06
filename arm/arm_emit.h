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

#ifndef ARM_EMIT_H
#define ARM_EMIT_H

#include "arm32_codegen.h"

extern "C" {
  void generate_indirect_branch_arm(void);
  void thumb_cheat_hook(void);
  void arm_cheat_hook(void);

  u32 arm_update_gba_arm(u32 pc);
  u32 arm_update_gba_thumb(u32 pc);
  u32 arm_update_gba_idle_arm(u32 pc);
  u32 arm_update_gba_idle_thumb(u32 pc);

  /* Although these are defined as a function, don't call them as
   * such (jump to it instead) */
  void arm_indirect_branch_arm(u32 address);
  void arm_indirect_branch_thumb(u32 address);
  void arm_indirect_branch_dual_arm(u32 address);
  void arm_indirect_branch_dual_thumb(u32 address);

  void execute_store_cpsr(u32 new_cpsr);
  u32 execute_spsr_restore_body(u32 pc);
  u32 execute_spsr_restore(u32 address);

  void execute_swi_arm(u32 pc);
  void execute_swi_thumb(u32 pc);
  u32 execute_arm_translate_internal(u32 cycles, void *regptr);

  void div_emu_sw6();
  void div_emu_sw7();
}

extern u32 st_handler_functions[4][17];
extern u32 ld_handler_functions[5][17];
extern u32 ld_swap_handler_functions[5][17];

// Tables used by the memory handlers (placed near reg_base)
extern u32 ld_lookup_tables[5][17];
extern u32 st_lookup_tables[4][17];

// Memory handler table offsets.
template <typename memtype> inline uintptr_t ldr_handler_offset();
template <typename memtype> inline uintptr_t str_handler_offset();

template <> inline u32 str_handler_offset<u8>()  { return 0; }
template <> inline u32 str_handler_offset<u16>() { return 1; }
template <> inline u32 str_handler_offset<u32>() { return 2; }
inline u32 safe_str_handler_offset() { return 3; }

template <> inline u32 ldr_handler_offset<u8>()  { return 4; }
template <> inline u32 ldr_handler_offset<s8>()  { return 5; }
template <> inline u32 ldr_handler_offset<u16>() { return 6; }
template <> inline u32 ldr_handler_offset<s16>() { return 7; }
template <> inline u32 ldr_handler_offset<u32>() { return 8; }


#define armfn_gbaup_idle_arm       0
#define armfn_gbaup_idle_thumb     1
#define armfn_gbaup_arm            2
#define armfn_gbaup_thumb          3
#define armfn_swi_arm              4
#define armfn_swi_thumb            5
#define armfn_cheat_arm            6
#define armfn_cheat_thumb          7
#define armfn_store_cpsr           8
#define armfn_spsr_restore         9
#define armfn_indirect_arm        10
#define armfn_indirect_thumb      11
#define armfn_indirect_dual_arm   12
#define armfn_indirect_dual_thumb 13
#define armfn_swi6_emu            14
#define armfn_swi7_emu            15
#define armfn_debug_trace_arm     16
#define armfn_debug_trace_thumb   17

#define STORE_TBL_OFF     0x118
#define SPSR_RAM_OFF      0x100

#define write32(value)                                                        \
  *((u32 *)this->emit_ptr) = value;                                           \
  this->emit_ptr += 4                                                         \

#define arm_relative_offset(source, offset)                                   \
  (((((u32)offset - (u32)source) - 8) >> 2) & 0xFFFFFF)                       \


#define reg_rv          armcg_reg0

#define reg_a0          armcg_reg0
#define reg_a1          armcg_reg1
#define reg_a2          armcg_reg2

#define reg_base        armcg_reg11
#define reg_flags       armcg_reg9

#define reg_cycles      armcg_reg12

#define reg_rm          armcg_reg0
#define reg_rn          armcg_reg1
#define reg_rs          armcg_reg14
#define reg_rd          armcg_reg0


/* Register allocation layout for ARM and Thumb:
 * Map from a GBA register to a host ARM register. -1 means load it
 * from memory into one of the temp registers.

 * The following registers are chosen based on statistical analysis
 * of a few games (see below), but might not be the best ones. Results
 * vary tremendously between ARM and Thumb (for obvious reasons), so
 * two sets are used. Take care to not call any function which can
 * overwrite any of these registers from the dynarec - only call
 * trusted functions in arm_stub.S which know how to save/restore
 * them and know how to transfer them to the C functions it calls
 * if necessary.

 * The following define the actual registers available for allocation.
 * As registers are freed up add them to this list.

 * Note that r15 is linked to the a0 temp reg - this register will
 * be preloaded with a constant upon read, and used to link to
 * indirect branch functions upon write.
 */

#define reg_x0         armcg_reg3
#define reg_x1         armcg_reg4
#define reg_x2         armcg_reg5
#define reg_x3         armcg_reg6
#define reg_x4         armcg_reg7
#define reg_x5         armcg_reg8

/*

ARM register usage (38.775138% ARM instructions):
r00: 18.263814% (-- 18.263814%)
r12: 11.531477% (-- 29.795291%)
r09: 11.500162% (-- 41.295453%)
r14: 9.063440% (-- 50.358893%)
r06: 7.837682% (-- 58.196574%)
r01: 7.401049% (-- 65.597623%)
r07: 6.778340% (-- 72.375963%)
r05: 5.445009% (-- 77.820973%)
r02: 5.427288% (-- 83.248260%)
r03: 5.293743% (-- 88.542003%)
r04: 3.601103% (-- 92.143106%)
r11: 3.207311% (-- 95.350417%)
r10: 2.334864% (-- 97.685281%)
r08: 1.708207% (-- 99.393488%)
r15: 0.311270% (-- 99.704757%)
r13: 0.295243% (-- 100.000000%)

Thumb register usage (61.224862% Thumb instructions):
r00: 34.788858% (-- 34.788858%)
r01: 26.564083% (-- 61.352941%)
r03: 10.983500% (-- 72.336441%)
r02: 8.303127% (-- 80.639567%)
r04: 4.900381% (-- 85.539948%)
r05: 3.941292% (-- 89.481240%)
r06: 3.257582% (-- 92.738822%)
r07: 2.644851% (-- 95.383673%)
r13: 1.408824% (-- 96.792497%)
r08: 0.906433% (-- 97.698930%)
r09: 0.679693% (-- 98.378623%)
r10: 0.656446% (-- 99.035069%)
r12: 0.453668% (-- 99.488737%)
r14: 0.248909% (-- 99.737646%)
r11: 0.171066% (-- 99.908713%)
r15: 0.091287% (-- 100.000000%)

*/

#define mem_reg     armcg_reginvalid

const armcg_regnum reg_alloc[2][16] = {
{ // ARM mode
  reg_x0,       /* GBA r0  */
  reg_x1,       /* GBA r1  */
  mem_reg,      /* GBA r2  */
  mem_reg,      /* GBA r3  */
  mem_reg,      /* GBA r4  */
  mem_reg,      /* GBA r5  */
  reg_x2,       /* GBA r6  */
  mem_reg,      /* GBA r7  */
  mem_reg,      /* GBA r8  */
  reg_x3,       /* GBA r9  */
  mem_reg,      /* GBA r10 */
  mem_reg,      /* GBA r11 */
  reg_x4,       /* GBA r12 */
  mem_reg,      /* GBA r13 */
  reg_x5,       /* GBA r14 */
  reg_a0,       /* GBA r15 */
},
{ // Thumb mode
  reg_x0,       /* GBA r0  */
  reg_x1,       /* GBA r1  */
  reg_x2,       /* GBA r2  */
  reg_x3,       /* GBA r3  */
  reg_x4,       /* GBA r4  */
  reg_x5,       /* GBA r5  */
  mem_reg,      /* GBA r6  */
  mem_reg,      /* GBA r7  */
  mem_reg,      /* GBA r8  */
  mem_reg,      /* GBA r9  */
  mem_reg,      /* GBA r10 */
  mem_reg,      /* GBA r11 */
  mem_reg,      /* GBA r12 */
  mem_reg,      /* GBA r13 */
  mem_reg,      /* GBA r14 */
  reg_a0,       /* GBA r15 */
}};

#define lshift_to_immshf(sa)   (((32 - sa) >> 1) & 15)


// TODO: New immediate generation, using mov/movn and orr/bic
u32 arm_disect_imm_32bit(u32 imm, u32 *stores, u32 *rotations)
{
  u32 store_count = 0;
  u32 left_shift = 0;

  /* Otherwise it'll return 0 things to store because it'll never
   * find anything. */
  if(imm == 0)
  {
    rotations[0] = 0;
    stores[0] = 0;
    return 1;
  }

  /* Find chunks of non-zero data at 2 bit alignments. */
  while(1)
  {
    for(; left_shift < 32; left_shift += 2)
    {
      if((imm >> left_shift) & 0x03)
        break;
    }

    /* We've hit the end of the useful data. */
    if(left_shift == 32)
      return store_count;

    /* Hit the end, it might wrap back around to the beginning. */
    if(left_shift >= 24)
    {
      /* Make a mask for the residual bits. IE, if we have
       * 5 bits of data at the end we can wrap around to 3
       * bits of data in the beginning. Thus the first
       * thing, after being shifted left, has to be less
       * than 111b, 0x7, or (1 << 3) - 1.
       */
      u32 top_bits = 32 - left_shift;
      u32 residual_bits = 8 - top_bits;
      u32 residual_mask = (1 << residual_bits) - 1;

      if((store_count > 1) && (left_shift > 24) &&
       ((stores[0] << ((32 - rotations[0]) & 0x1F)) < residual_mask))
      {
        /* Then we can throw out the last bit and tack it on
         * to the first bit. */
        stores[0] =
         (stores[0] << ((top_bits + (32 - rotations[0])) & 0x1F)) |
         ((imm >> left_shift) & 0xFF);
        rotations[0] = top_bits;

        return store_count;
      }
      else
      {
        /* There's nothing to wrap over to in the beginning */
        stores[store_count] = (imm >> left_shift) & 0xFF;
        rotations[store_count] = (32 - left_shift) & 0x1F;
        return store_count + 1;
      }
      break;
    }

    stores[store_count] = (imm >> left_shift) & 0xFF;
    rotations[store_count] = (32 - left_shift) & 0x1F;

    store_count++;
    left_shift += 8;
  }
}


#define generate_load_pc(ireg, new_pc)                                        \
  load_imm32(ireg, new_pc)                                                    \

#define generate_add_imm(ireg, imm, imm_ror)                                  \
  emit_alu_imm<OpAdd, NoFlags>(ireg, ireg, imm_ror, imm);

/* Calls functions that might be far, via the function table at reg_base */
#define generate_function_far_call(function_number)                           \
  load_memreg(armcg_reglr, function_number + (u32)REG_USERDEF);               \
  emit_blx(armcg_reglr)                                                       \

/* The branch target is to be filled in later (thus a 0 for now) */

#define generate_branch_filler(condition_code, writeback_location)            \
  (writeback_location) = this->emit_ptr;                                      \
  emit_bcond(condition_code, 0);

#define generate_update_pc(new_pc)                                            \
  generate_load_pc(reg_a0, new_pc)                                            \

#define generate_branch_patch_conditional(dest, offset)                       \
  *((u32 *)(dest)) = (*((u32 *)dest) & 0xFF000000) |                          \
   arm_relative_offset(dest, offset)                                          \


#define generate_branch_patch_unconditional(dest, offset)                     \
  *((u32 *)(dest)) = (*((u32 *)dest) & 0xFF000000) |                          \
   arm_relative_offset(dest, offset)                                          \

/* A different function is called for idle updates because of the relative
 * location of the embedded PC. The idle version could be optimized to put
 * the CPU into halt mode too, however.
 */

#define generate_branch_idle_eliminate(writeback_location, new_pc, mode)      \
  generate_function_far_call(armfn_gbaup_idle_##mode);                        \
  write32(new_pc);                                                            \
  generate_branch_filler(CondAL, writeback_location)                          \

#define generate_branch_update(writeback_location, new_pc, mode)              \
  emit_mov_reg_immshift<OpMov, NoFlags>(reg_a0, reg_cycles, ShiftLSR, 31);    \
  /* If counter is negative, skip the update call (2 insts) */                \
  emit_alu_reg_immshift<OpAdd, NoFlags>(armcg_regpc, armcg_regpc, reg_a0, ShiftLSL, 3); \
  write32(new_pc);                                                            \
  generate_function_far_call(armfn_gbaup_##mode);   /* 2 instructions */      \
  generate_branch_filler(CondAL, writeback_location)                          \


#define generate_branch_no_cycle_update(writeback_location, new_pc, mode)     \
  if(pc == idle_loop_target_pc) {                                             \
    generate_branch_idle_eliminate(writeback_location, new_pc, mode);         \
  } else {                                                                    \
    generate_branch_update(writeback_location, new_pc, mode);                 \
  }                                                                           \

#define generate_branch_cycle_update(writeback_location, new_pc, mode)        \
  emit_cycle_update();                                                        \
  generate_branch_no_cycle_update(writeback_location, new_pc, mode)           \

/* a0 holds the destination */

#define generate_indirect_branch_no_cycle_update(type)                        \
  emit_ldr_imm(armcg_regpc, reg_base, 4*(REG_USERDEF + armfn_indirect_##type));

#define generate_indirect_branch_cycle_update(type)                           \
  emit_cycle_update();                                                        \
  generate_indirect_branch_no_cycle_update(type)                              \

#define generate_indirect_branch_arm() {                                      \
    if(condition == 0x0E) {                                                   \
      emit_cycle_update();                                                    \
    }                                                                         \
    generate_indirect_branch_no_cycle_update(arm);                            \
  }                                                                           \

#define generate_indirect_branch_dual() {                                     \
    if(condition == 0x0E) {                                                   \
      emit_cycle_update();                                                    \
    }                                                                         \
    generate_indirect_branch_no_cycle_update(dual_arm);                       \
  }                                                                           \


#define arm_complete_store_reg_pc_no_flags(scratch_reg, reg_index) {          \
  if(reg_index == REG_PC) {                                                   \
    generate_indirect_branch_arm();                                           \
  } else {                                                                    \
    complete_store_reg<ModeARM>(scratch_reg, reg_index);                      \
  }                                                                           \
}                                                                             \

#define arm_complete_store_reg_pc_flags(scratch_reg, reg_index) {             \
  if (reg_index == REG_PC) {                                                  \
    if(condition == 0x0E) {                                                   \
      emit_cycle_update();                                                    \
    }                                                                         \
    generate_function_far_call(armfn_spsr_restore);                           \
  } else {                                                                    \
    complete_store_reg<ModeARM>(scratch_reg, reg_index);                      \
  }                                                                           \
}                                                                             \

u32 execute_spsr_restore_body(u32 pc) {
  set_cpu_mode(cpu_modes[reg[REG_CPSR] & 0xF]);

  if ((io_registers[REG_IE] & io_registers[REG_IF]) &&
      io_registers[REG_IME] && ((reg[REG_CPSR] & 0x80) == 0)) {
    REG_MODE(MODE_IRQ)[6] = pc + 4;
    REG_SPSR(MODE_IRQ) = reg[REG_CPSR];
    reg[REG_CPSR] = 0xD2;
    pc = 0x00000018;
    set_cpu_mode(MODE_IRQ);
  }

  return pc;
}

#define generate_branch(mode) {                                               \
  generate_branch_cycle_update(                                               \
   block_exits[block_exit_position].branch_source,                            \
   block_exits[block_exit_position].branch_target, mode);                     \
  block_exit_position++;                                                      \
}                                                                             \


#define generate_load_call(tblnum, abits)                                     \
  mem_calc_region(abits);                                                     \
  generate_add_imm(reg_a2, (STORE_TBL_OFF + 68*tblnum + 4) >> 2, 0);          \
  emit_ldr_reg(reg_a2, reg_base, reg_a2, ShiftLSL, 2);                        \
  emit_blx(reg_a2);                                                           \

#define generate_store_call(tblnum)                                           \
  mem_calc_region(0);                                                         \
  generate_add_imm(reg_a2, (STORE_TBL_OFF + 68*tblnum + 4) >> 2, 0);          \
  emit_ldr_reg(reg_a2, reg_base, reg_a2, ShiftLSL, 2);                        \
  emit_blx(reg_a2);                                                           \


#define generate_store_call_u8()        generate_store_call(0)
#define generate_store_call_u16()       generate_store_call(1)
#define generate_store_call_u32()       generate_store_call(2)
#define generate_store_call_u32_safe()  generate_store_call(3)
#define generate_load_call_u8()         generate_load_call(4, 0)
#define generate_load_call_s8()         generate_load_call(5, 0)
#define generate_load_call_u16()        generate_load_call(6, 1)
#define generate_load_call_s16()        generate_load_call(7, 1)
#define generate_load_call_u32()        generate_load_call(8, 2)


class CodeEmitter : public ARMEmitter {
public:
  CodeEmitter(u8 *emit_ptr, u32 pc)
   : ARMEmitter(emit_ptr) {}

  static unsigned block_header_size() { return 0; }
  inline void emit_block_header() {}
  inline void emit_block_prologue() {}

  inline void load_imm32(armcg_regnum reg, u32 value) {
    #if __ARM_ARCH >= 7
      emit_movw(reg, value);
      if (value >> 16)
        emit_movt(reg, value >> 16);
    #else
      u32 stores[4], rotations[4];
      u32 store_count = arm_disect_imm_32bit(value, stores, rotations);

      emit_mov_imm<OpMov, NoFlags>(reg, rotations[0] >> 1, stores[0]);
      for(unsigned i = 1; i < store_count; i++)
        emit_alu_imm<OpOrr, NoFlags>(reg, reg, rotations[i] >> 1, stores[i]);
    #endif
  }

  inline void load_memreg(armcg_regnum dreg, u32 regnum) {
    emit_ldr_imm(dreg, reg_base, regnum * 4);
  }
  inline void store_memreg(armcg_regnum sreg, u32 regnum) {
    emit_str_imm(sreg, reg_base, regnum * 4);
  }

  // Returns the register number and loads it to a scratch reg if needed.
  template <CPUInstMode cpum>
  inline armcg_regnum prepare_load_loreg(armcg_regnum scratch_reg, u32 reg_index) {
    armcg_regnum regn = reg_alloc[cpum][reg_index];
    if (regn != mem_reg)
      return regn;

    emit_ldr_imm(scratch_reg, reg_base, reg_index * 4);
    return scratch_reg;
  }

  template <CPUInstMode cpum>
  inline armcg_regnum prepare_load_reg(armcg_regnum scratch_reg, u32 reg_index, u32 pc, u32 instoff) {
    if (reg_index == REG_PC) {
      const u32 isz = (cpum == ModeARM) ? 4 : 2;
      load_imm32(scratch_reg, pc + instoff * isz);
      return scratch_reg;
    }

    return prepare_load_loreg<cpum>(scratch_reg, reg_index);
  }

  // Forces a register load into the destination register (including PC value)
  template <CPUInstMode cpum>
  inline void force_load_reg(armcg_regnum dest_reg, u32 reg_index, u32 pc_value) {
    if (reg_index == REG_PC)
      load_imm32(dest_reg, pc_value);
    else {
      armcg_regnum regn = reg_alloc[cpum][reg_index];
      if (regn != mem_reg)
        emit_mov_reg_immshift<OpMov, NoFlags>(dest_reg, regn);
      else
        emit_ldr_imm(dest_reg, reg_base, reg_index * 4);
    }
  }

  template <CPUInstMode cpum>
  inline armcg_regnum prepare_store_reg(armcg_regnum scratch_reg, u32 reg_index) {
    armcg_regnum regn = reg_alloc[cpum][reg_index];
    if (regn == mem_reg)
      return scratch_reg;

    return regn;
  }

  template <CPUInstMode cpum>
  inline void complete_store_reg(armcg_regnum scratch_reg, u32 reg_index) {
    armcg_regnum regn = reg_alloc[cpum][reg_index];
    if (regn == mem_reg)
      emit_str_imm(scratch_reg, reg_base, reg_index * 4);
  }

  // Stores a register value back to its register or memory.
  template <CPUInstMode cpum>
  inline void force_store_reg(armcg_regnum reg, u32 reg_index) {
    armcg_regnum regn = reg_alloc[cpum][reg_index];
    if (regn != mem_reg)
      emit_mov_reg_immshift<OpMov, NoFlags>(regn, reg);
    else
      emit_str_imm(reg, reg_base, reg_index * 4);
  }

  inline void emit_addsub8(armcg_regnum dreg, armcg_regnum sreg, int imm, u32 shifta = 0) {
    if (imm >= 0)
      emit_alu_imm<OpAdd, NoFlags>(dreg, sreg, shifta, imm);
    else
      emit_alu_imm<OpSub, NoFlags>(dreg, sreg, shifta, -imm);
  }

  inline void mem_calc_region(unsigned numbits) {
    // We use USAT + ROR to map addresses to the handler table. For ARMv5 we use
    // the table -1 entry to map any out of range/unaligned access, and some fun
    // math/logical tricks to avoid using USAT.

    #if __ARM_ARCH >= 6
      if (!numbits)
        emit_usat_asr(reg_a2, 4, reg_a0, 24);
      else {
        emit_mov_reg_immshift<OpMov, NoFlags>(reg_a2, reg_a0, ShiftROR, numbits);
        emit_usat_asr(reg_a2, 4, reg_a2, 24-numbits);
      }
    #else
      if (!numbits)
        emit_mov_reg_immshift<OpMov, NoFlags>(reg_a2, reg_a0, ShiftLSR, 24);
      else {
        emit_alu_imm<OpOrr, NoFlags>(reg_a2, reg_a0, ShiftLSL, 32-numbits);
        emit_mov_reg_immshift<OpMov, NoFlags>(reg_a2, reg_a2, ShiftLSR, 24);
      }
      emit_alu_imm<OpRsb, NoFlags>(armcg_reglr, reg_a2, 0, 15);
      emit_alu_reg_immshift<OpOrr, NoFlags>(reg_a2, reg_a2, armcg_reglr, ShiftASR, 31);
    #endif
  }

  template <CPUInstMode cm>
  inline void generate_translation_gate(u32 pc) {
    generate_update_pc(pc);
    if (cm == ModeARM)
      emit_ldr_imm(armcg_regpc, reg_base, 4*(REG_USERDEF + armfn_indirect_arm));
    else
      emit_ldr_imm(armcg_regpc, reg_base, 4*(REG_USERDEF + armfn_indirect_thumb));
  }

  inline void emit_cycle_update() {
    if (cyc_cnt) {
      if (cyc_cnt >> 8)
        emit_alu_imm<OpAdd, NoFlags>(reg_cycles, reg_cycles, lshift_to_immshf(8), cyc_cnt >> 8);
      emit_alu_imm<OpAdd, NoFlags>(reg_cycles, reg_cycles, 0, cyc_cnt & 0xFF);
      cyc_cnt = 0;
    }
  }

  template <CPUInstMode cm>
  inline void emit_cheat_hook() {
    if (cm == ModeARM) {
      generate_function_far_call(armfn_cheat_arm);
    } else {
      generate_function_far_call(armfn_cheat_thumb);
    }
  }

  inline void arm_conditional_block_header(u32 condition, u8 * & backpatch_address) {
    emit_cycle_update();
    /* This will choose the opposite condition */
    condition ^= 0x01;
    generate_branch_filler(condition, backpatch_address);
  }


  // ======================================================
  // ================ Thumb instructions ==================
  // ======================================================
  void thumb_invalid(const ThumbInst & it) {
    // Do nothing on purpose.
  }

  template <ARMOp aluop>
  void thumb_aluop3(const ThumbInst & it) {
    armcg_regnum rs = prepare_load_loreg<ModeThumb>(reg_rs, it.rs());
    armcg_regnum rn = prepare_load_loreg<ModeThumb>(reg_rn, it.rn());
    armcg_regnum rd = prepare_store_reg<ModeThumb>(reg_rd, it.rd());
    emit_alus_reg<aluop>(rd, rs, rn);
    complete_store_reg<ModeThumb>(reg_rd, it.rd());
  }

  template <ARMOp aluop>
  void thumb_aluop2(const ThumbInst & it) {
    armcg_regnum rs = prepare_load_loreg<ModeThumb>(reg_rs, it.rs());
    armcg_regnum rd = prepare_load_loreg<ModeThumb>(reg_rd, it.rd());

    if (aluop == OpMul)
      emit_mul<SetFlags>(rd, rd, rs);
    else
      emit_alus_reg<aluop>(rd, rd, rs);

    complete_store_reg<ModeThumb>(reg_rd, it.rd());
  }

  template <ARMOp aluop>
  void thumb_aluop1(const ThumbInst & it) {
    armcg_regnum rs = prepare_load_loreg<ModeThumb>(reg_rs, it.rs());
    armcg_regnum rd = prepare_store_reg<ModeThumb>(reg_rd, it.rd());

    switch (aluop) {
    case OpNeg: emit_alu_imm<OpRsb, SetFlags>(rd, rs, 0, 0);    break;
    case OpMvn: emit_mov_reg_immshift<OpMvn, SetFlags>(rd, rs); break;
    };

    complete_store_reg<ModeThumb>(reg_rd, it.rd());
  }

  template <OpType stype, ShiftType st>
  void thumb_shft(const ThumbInst & it) {
    armcg_regnum rd = prepare_store_reg<ModeThumb>(reg_rd, it.rd());
    armcg_regnum rs = prepare_load_loreg<ModeThumb>(reg_rs, it.rs());

    if (stype == OpImm)
      emit_mov_reg_immshift<OpMov, SetFlags>(rd, rs, st, it.imm5());
    else {
      armcg_regnum rm = prepare_load_loreg<ModeThumb>(reg_rd, it.rd());
      emit_mov_reg_regshift<OpMov, SetFlags>(rd, rm, st, rs);
    }

    complete_store_reg<ModeThumb>(rd, it.rd());
  }

  template <ARMOp aluop>
  void thumb_aluimm2(const ThumbInst & it) {
    switch (aluop) {
    case OpMov:
      {
        armcg_regnum rd = prepare_store_reg<ModeThumb>(reg_rd, it.rd8());
        emit_mov_imm<OpMov, SetFlags>(rd, 0, it.imm8());
        complete_store_reg<ModeThumb>(reg_rd, it.rd8());
      }
      break;
    case OpAdd:
    case OpSub:
      {
        armcg_regnum rd = prepare_load_loreg<ModeThumb>(reg_rd, it.rd8());
        emit_alus_imm<aluop>(rd, rd, it.imm8());
        complete_store_reg<ModeThumb>(reg_rd, it.rd8());
      }
      break;
    case OpCmp:
      {
        armcg_regnum rd = prepare_load_loreg<ModeThumb>(reg_rd, it.rd8());
        emit_test_imm<OpCmp>(rd, 0, it.imm8());
      }
      break;
    };
  }

  template <ARMOp aluop>
  void thumb_aluimm3(const ThumbInst & it) {
    armcg_regnum rs = prepare_load_loreg<ModeThumb>(reg_rs, it.rs());
    armcg_regnum rd = prepare_store_reg<ModeThumb>(reg_rd, it.rd());
    emit_alus_imm<aluop>(rd, rs, it.imm3());
    complete_store_reg<ModeThumb>(reg_rd, it.rd());
  }

  template <ARMOp testop>
  void thumb_testop(const ThumbInst & it) {
    armcg_regnum rs = prepare_load_loreg<ModeThumb>(reg_rs, it.rs());
    armcg_regnum rd = prepare_load_loreg<ModeThumb>(reg_rd, it.rd());
    emit_test_reg_immshift<testop>(rd, rs);
  }

  template <ARMOp aluop>
  void thumb_aluhi(const ThumbInst & it) {
    armcg_regnum rs = prepare_load_reg<ModeThumb>(reg_rn, it.rs_hi(), it.pc, 2);

    armcg_regnum rd = (aluop == OpAdd || aluop == OpCmp) ? prepare_load_reg<ModeThumb>(reg_rd, it.rd_hi(), it.pc, 2)
                                                         : prepare_store_reg<ModeThumb>(reg_rd, it.rd_hi());

    if (aluop == OpAdd)
      emit_alu_reg_immshift<OpAdd, NoFlags>(rd, rd, rs);
    else if (aluop == OpCmp)
      emit_test_reg_immshift<OpCmp>(rd, rs);
    else if (aluop == OpMov)
      emit_mov_reg_immshift<OpMov, NoFlags>(rd, rs);

    if (aluop == OpAdd || aluop == OpMov) {
      if (it.rd_hi() != REG_PC)
        complete_store_reg<ModeThumb>(rd, it.rd_hi());
      else {
        generate_indirect_branch_cycle_update(thumb);
      }
    }
  }

  template <u32 ref_reg>
  void thumb_regoff(const ThumbInst & it) {
    if (ref_reg == REG_PC) {
      armcg_regnum rd = prepare_store_reg<ModeThumb>(reg_rd, it.rd8());
      generate_load_pc(rd, (it.pc & ~2) + 4 + 4 * it.imm8());
    } else {
      armcg_regnum sreg = prepare_load_loreg<ModeThumb>(reg_a0, ref_reg);
      armcg_regnum rd = prepare_store_reg<ModeThumb>(reg_rd, it.rd8());
      emit_alu_imm<OpAdd, NoFlags>(rd, sreg, lshift_to_immshf(2), it.imm8());
    }

    complete_store_reg<ModeThumb>(reg_rd, it.rd8());
  }

  void thumb_spadj(const ThumbInst & it) {
    armcg_regnum sp = prepare_load_loreg<ModeThumb>(reg_a0, REG_SP);
    emit_addsub8(sp, sp, it.imm71(), lshift_to_immshf(2));
    complete_store_reg<ModeThumb>(reg_a0, REG_SP);
  }

  void thumb_bx(const ThumbInst & it) {
    force_load_reg<ModeThumb>(reg_a0, it.rs_hi(), it.pc + 4);
    generate_indirect_branch_cycle_update(dual_thumb);
  }

  void thumb_blh(const ThumbInst & it) {
    u32 offlo = it.abr_offset_lo() & 0xFF;
    u32 offhi = it.abr_offset_lo() >> 8;

    generate_update_pc(((it.pc + 2) | 0x01));
    force_load_reg<ModeThumb>(reg_a1, REG_LR, it.pc + 4);
    force_store_reg<ModeThumb>(reg_a0, REG_LR);

    emit_alu_imm<OpAdd, NoFlags>(reg_a0, reg_a1, 0, offlo);
    if (offhi)
      emit_alu_imm<OpAdd, NoFlags>(reg_a0, reg_a0, lshift_to_immshf(8), offhi);

    generate_indirect_branch_cycle_update(thumb);
  }

  inline void arm_bx(const ARMInst & it) {
    const u8 condition = it.cond();        // TODO remove this
    force_load_reg<ModeARM>(reg_a0, it.rm(), it.pc + 8);
    generate_indirect_branch_dual();
  }

  static bool can_emu_swi(u32 pc, u32 num) {
    return (num == 6 || num == 7);
  }

  template <CPUInstMode cpum, typename iclass>
  void emu_swi(const iclass &it) {
    const u32 num = it.swinum();

    cyc_cnt += 64;
    generate_function_far_call((num == 6 ? armfn_swi6_emu : armfn_swi7_emu));
  }

  u8* thumb_swi(u32 pc, u32 target) {
    u8 *brtgt = NULL;

    generate_function_far_call(armfn_swi_thumb);
    write32((pc + 2));
    generate_branch_cycle_update(brtgt, target, arm);

    return brtgt;
  }

  inline u8* arm_swi(u32 pc) {
    u8 *brtgt = NULL;

    generate_function_far_call(armfn_swi_arm);
    write32((pc + 4));
    generate_branch_cycle_update(brtgt, 0x00000008, arm);

    return brtgt;
  }

  template <ARMCondCode ccode>
  u8* thumb_brcond(u32 pc, u32 target) {
    u8 *brtgt = NULL;
    u8 *ptch = NULL;

    u32 oppcode = (ccode ^ 0x01);   // Simple opposite code conversion!

    emit_cycle_update();
    generate_branch_filler(oppcode, ptch);
    generate_branch_no_cycle_update(brtgt, target, thumb);
    generate_branch_patch_conditional(ptch, this->emit_ptr);
    return brtgt;
  }

  u8* thumb_b(u32 pc, u32 target) {
    u8 *brtgt = NULL;
    generate_branch_cycle_update(brtgt, target, thumb);
    return brtgt;
  }

  inline u8* arm_b(const ARMInst & it, u32 target) {
    const u32 pc = it.pc;  // TODO: Remove this
    u8 *brtgt = NULL;
    if (it.cond() == CondAL) {
      generate_branch_cycle_update(brtgt, target, arm);
    } else {
      generate_branch_no_cycle_update(brtgt, target, arm);
    }
    return brtgt;
  }

  u8* thumb_bl(u32 pc, u32 target) {
    u8 *brtgt = NULL;
    generate_update_pc(((pc + 2) | 0x01));
    force_store_reg<ModeThumb>(reg_a0, REG_LR);
    generate_branch_cycle_update(brtgt, target, thumb);
    return brtgt;
  }

  inline u8* arm_bl(const ARMInst & it, u32 target) {
    const u32 pc = it.pc;  // TODO: Remove this
    u8 *brtgt = NULL;
    generate_update_pc(pc + 4);
    force_store_reg<ModeARM>(reg_a0, REG_LR);
    if (it.cond() == CondAL) {
      generate_branch_cycle_update(brtgt, target, arm);
    } else {
      generate_branch_no_cycle_update(brtgt, target, arm);
    }
    return brtgt;
  }

  // ============= Memory functions =================
  template <bool onram>
  void thumb_loadpool(const ThumbInst & it) {
    const u32 daddr = 4 + it.imm8() * 4 + (it.pc & ~3U);
    if (!onram && (daddr >> 15) == (it.pc >> 15)) {
      u8 *blkb = memory_map_read[it.pc >> 15];
      u32 value = address32(blkb, (daddr & 0x7FFF));
      armcg_regnum rgdst = prepare_store_reg<ModeThumb>(reg_a0, it.rd8());
      load_imm32(rgdst, value);
      complete_store_reg<ModeThumb>(rgdst, it.rd8());
    } else {
      cyc_cnt += 2;      // TODO: We can calculate this here rather precisely.

      u32 ldtype = ldr_handler_offset<u32>();
      emit_ldr_imm(reg_a2, reg_base, (daddr >> 24) * 4 + (STORE_TBL_OFF + 68*ldtype + 4));
      load_imm32(reg_a0, daddr);
      emit_blx(reg_a2);
      write32(it.pc);
      force_store_reg<ModeThumb>(reg_rv, it.rd8());
    }
  }

  template <AccMode memmode, typename memtype, ThumbMemOffset offt>
  void thumb_memacc(const ThumbInst & it) {
    cyc_cnt += (memmode == AccLoad) ? 2 : 1;  // TODO: Use proper cycle accounting and honor WAITCNT

    const u32 basereg = (offt == OffSP) ? REG_SP : it.rb();
    armcg_regnum rb = prepare_load_loreg<ModeThumb>(reg_a0, basereg);
    if (offt == OffReg) {
      armcg_regnum ro = prepare_load_loreg<ModeThumb>(reg_a1, it.ro());
      emit_alu_reg_immshift<OpAdd, NoFlags>(reg_a0, rb, ro);
    }
    else if (offt == OffImm5)
      emit_alu_imm<OpAdd, NoFlags>(reg_a0, rb, 0, it.imm5() * sizeof(memtype));
    else
      emit_alu_imm<OpAdd, NoFlags>(reg_a0, rb, lshift_to_immshf(2), it.imm8());

    const u32 datareg = (offt == OffSP) ? it.rd8() : it.rd();
    // Generate a call to the right memory section handler.
    if (memmode == AccLoad) {
      u32 ldtype = ldr_handler_offset<memtype>();
      u32 nbits = sizeof(memtype) / 2;  // log2(size)
      mem_calc_region(nbits);
      generate_add_imm(reg_a2, (STORE_TBL_OFF + 68*ldtype + 4) >> 2, 0);
      emit_ldr_reg(reg_a2, reg_base, reg_a2, ShiftLSL, 2);
      emit_blx(reg_a2);
      write32(it.pc);
      force_store_reg<ModeThumb>(reg_rv, datareg);
    } else {
      u32 sttype = str_handler_offset<memtype>();
      mem_calc_region(0);
      generate_add_imm(reg_a2, (STORE_TBL_OFF + 68*sttype + 4) >> 2, 0);
      emit_ldr_reg(reg_a2, reg_base, reg_a2, ShiftLSL, 2);
      force_load_reg<ModeThumb>(reg_a1, datareg, it.pc + 4);
      emit_blx(reg_a2);
      write32((it.pc + 2));
    }
  }

  template <ARMMemOffset offt, MemOffDir dir>
  inline void arm_memaddr(armcg_regnum oreg, const ARMInst & it) {
    // Load base register if needed
    armcg_regnum breg = prepare_load_reg<ModeARM>(oreg, it.rn(), it.pc, 2);
    constexpr ARMOp aop = dir == OffPositive ? OpAdd : OpSub;

    switch (offt) {
    case OffImm12:     // [rn +/- imm12]
      // Try to minimize the number of instructions we need to calculate the -/+12 offset.
      if (it.off12() < 256)
        emit_alu_imm<aop, NoFlags>(oreg, breg, 0, it.off12());
      else if (!(it.off12() & 0xF))
        emit_alu_imm<aop, NoFlags>(oreg, breg, lshift_to_immshf(4), it.off12() >> 4);
      else if (!(it.off12() & 0xC03))
        emit_alu_imm<aop, NoFlags>(oreg, breg, lshift_to_immshf(2), it.off12() >> 2);
      else {
        emit_alu_imm<aop, NoFlags>(oreg, breg, 0, it.off12() & 0xFF);
        emit_alu_imm<aop, NoFlags>(oreg, oreg, lshift_to_immshf(8), it.off12() >> 8);
      }
      break;
    case OffHImm8:     // [rn +/- imm8]
      emit_alu_imm<aop, NoFlags>(oreg, breg, 0, it.off8());
      break;
    case OffHReg:      // [rn +/- rm]
      {
        armcg_regnum secreg = prepare_load_reg<ModeARM>(reg_a2, it.rm(), it.pc, 2);
        emit_alu_reg_immshift<aop, NoFlags>(oreg, breg, secreg);
      }
      break;
    case OffOp2Reg:    // [rn +/- rm shift/rot amount]
      {
        armcg_regnum secreg = prepare_load_reg<ModeARM>(reg_a2, it.rm(), it.pc, 2);
        emit_alu_reg_immshift<aop, NoFlags>(oreg, breg, secreg, it.op2smode(), it.op2sa());
      }
      break;
    };
  }

  template <typename memtype, ARMMemOffset offt, MemOffDir dir, MemIdxMode idxm>
  inline void arm_memst(const ARMInst & it) {
    cyc_cnt++;    // TODO: Use proper cycle accounting and honor WAITCNT

    // Generate the final address and base address, and write back if necessary
    if (idxm == MemIdxPostWB) {
      // Load the base reg to a0
      force_load_reg<ModeARM>(reg_a0, it.rn(), it.pc + 4);
      // Calculate the final value to the final reg.
      armcg_regnum wbreg = prepare_store_reg<ModeARM>(reg_a1, it.rn());
      arm_memaddr<offt, dir>(wbreg, it);
      complete_store_reg<ModeARM>(wbreg, it.rn());
    }
    else {
      arm_memaddr<offt, dir>(reg_a0, it);  // Calculate final addr to a0
      if (idxm == MemIdxPreWB)
        force_store_reg<ModeARM>(reg_a0, it.rn());
    }

    // Generate call to handler, load the value to write to a1
    force_load_reg<ModeARM>(reg_a1, it.rd(), it.pc + 12);
    generate_store_call(str_handler_offset<memtype>());
    write32((it.pc + 4));
  }

  template <typename memtype, ARMMemOffset offt, MemOffDir dir, MemIdxMode idxm>
  inline void arm_memld(const ARMInst & it) {
    const u8 condition = it.cond();        // TODO remove this
    cyc_cnt += 2;    // TODO: Use proper cycle accounting and honor WAITCNT

    // Generate the final address and base address, and write back if necessary
    if (idxm == MemIdxPostWB) {
      // Load the base reg to a0
      force_load_reg<ModeARM>(reg_a0, it.rn(), it.pc + 4);
      // Calculate the final value to the final reg.
      armcg_regnum wbreg = prepare_store_reg<ModeARM>(reg_a1, it.rn());
      arm_memaddr<offt, dir>(wbreg, it);
      complete_store_reg<ModeARM>(wbreg, it.rn());
    }
    else {
      arm_memaddr<offt, dir>(reg_a0, it);  // Calculate final addr to a0
      if (idxm == MemIdxPreWB)
        force_store_reg<ModeARM>(reg_a0, it.rn());
    }

    // Generate call to handler, load the value to write to a1
    generate_store_call(ldr_handler_offset<memtype>());
    write32(it.pc);

    if (it.rd() == REG_PC) {
      generate_indirect_branch_arm();
    } else {
      force_store_reg<ModeARM>(reg_rv, it.rd());
    }
  }

  template <typename memtype>
  inline void arm_swap(const ARMInst & it) {
    cyc_cnt += 3;   // TODO: Some more accurate accounting :)

    // rd = mem[rn], mem[rn] = rm (Note: all regs could be the same!)

    force_load_reg<ModeARM>(reg_a0, it.rn(), it.pc + 4);
    generate_store_call(ldr_handler_offset<memtype>());
    write32(it.pc);

    emit_mov_reg_immshift<OpMov, NoFlags>(reg_a2, reg_rv);
    force_load_reg<ModeARM>(reg_a0, it.rn(), it.pc + 4);
    force_load_reg<ModeARM>(reg_a1, it.rm(), it.pc + 4);
    force_store_reg<ModeARM>(reg_a2, it.rd());
    generate_store_call(str_handler_offset<memtype>());
    write32((it.pc + 4));
  }

  template <CPUInstMode cpum, AccMode amode, AddrMode addrmode, bool writeback, bool sbit>
  inline void mem_multi(u32 pc, u32 condition, u32 basereg, u16 rlist) {
    const u32 numops = bit_count[rlist >> 8] + bit_count[rlist & 0xFF];
    cyc_cnt += numops;    // TODO: Use proper cycle accounting.

    const u32 itsize = (cpum == ModeARM) ? 4 : 2;
    const s32 stpoff = (addrmode == AddrPreInc || addrmode == AddrPostInc) ? 4 : -4;
    const s32 endoff = stpoff * numops;
    const s32 inioff = (addrmode == AddrPreInc)  ? 4 :
                       (addrmode == AddrPostInc) ? 0 :
                       (addrmode == AddrPreDec)  ? endoff :
                                                   endoff + 4;

    // Load base register, clear its lower bits.
    armcg_regnum nreg = prepare_load_reg<cpum>(reg_a1, basereg, pc, 2);
    emit_alu_imm<OpBic, NoFlags>(reg_a0, nreg, 0, 0x03);
    store_memreg(reg_a0, REG_SAVE);

    // If base is in the reglist and writeback is enabled, the value of the
    // written register depends on the write cycle (ARM7TDM manual 4.11.6).
    // If the register is the first, the written value is the original value,
    // otherwise the update base register is written. For LDM loaded data
    // takes always precendence.
    bool wrbck_base = (1 << basereg) & rlist;
    bool base_first = (((1 << basereg) - 1) & rlist) == 0;
    bool writeback_first = (amode == AccLoad) || !(wrbck_base && base_first);

    // This is the most common case by far.
    if (writeback && writeback_first) {
      // TODO: Improve this!
      armcg_regnum scratch = prepare_store_reg<cpum>(reg_a2, basereg);
      emit_addsub8(scratch, nreg, endoff);
      complete_store_reg<cpum>(scratch, basereg);
    }

    u32 aoff = 0;
    for (u32 i = 0; i < 16; i++) {
      if (rlist & (1 << i)) {
        load_memreg(reg_a0, REG_SAVE);
        emit_addsub8(reg_a0, reg_a0, (aoff + inioff));
        if (amode == AccLoad) {
          u32 ldtype = ldr_handler_offset<u32>();
          mem_calc_region(0);
          generate_add_imm(reg_a2, (STORE_TBL_OFF + 68*ldtype + 4) >> 2, 0);
          emit_ldr_reg(reg_a2, reg_base, reg_a2, ShiftLSL, 2);
          emit_blx(reg_a2);
          write32(pc + itsize);
          force_store_reg<cpum>(reg_rv, i);
        } else {
          force_load_reg<cpum>(reg_a1, i, pc + 12);

          // Update the base register right after the first read if necessary
          if (writeback && !writeback_first) {
            armcg_regnum scratch = prepare_load_reg<cpum>(reg_a1, basereg, pc, 2);
            emit_addsub8(scratch, scratch, endoff);
            complete_store_reg<cpum>(scratch, basereg);
            writeback_first = true;
          }

          if (rlist >> (i + 1)) {
            generate_store_call_u32_safe();
          } else {
            generate_store_call_u32();
            write32(pc + itsize);
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

  template <AccMode amode, AddrMode addrmode>
  void thumb_memmulti(const ThumbInst & it) {
    this->mem_multi<ModeThumb, amode, addrmode, true, false>(it.pc, 0, it.rptr(), it.rlist());
  }

  template <AccMode amode, AddrMode addrmode, unsigned extraregm = 0>
  void thumb_pushpop(const ThumbInst & it) {
    this->mem_multi<ModeThumb, amode, addrmode, true, false>(it.pc, 0, REG_SP, it.rlist() | extraregm);
  }

  // ======== ARM instructions ======================================
  template <ARMOp aluop, FlagOperation flg>
  inline void arm_aluimm3(const ARMInst & it) {
    armcg_regnum rn = prepare_load_reg<ModeARM>(reg_rn, it.rn(), it.pc, 2);
    armcg_regnum rd = prepare_store_reg<ModeARM>(reg_rd, it.rd());

    emit_alu_imm<aluop, flg>(rd, rn, it.rot4(), it.imm8());

    const u8 condition = it.cond();        // TODO remove this
    if (flg == SetFlags) {
      arm_complete_store_reg_pc_flags(reg_rd, it.rd());
    } else {
      arm_complete_store_reg_pc_no_flags(reg_rd, it.rd());
    }
  }

  template <ARMOp aluop>
  inline void arm_aluimm2(const ARMInst & it) {
    armcg_regnum rn = prepare_load_reg<ModeARM>(reg_rn, it.rn(), it.pc, 2);
    emit_test_imm<aluop>(rn, it.rot4(), it.imm8());
  }

  template <ARMOp aluop, FlagOperation flg>
  inline void arm_aluimm1(const ARMInst & it) {
    armcg_regnum rd = prepare_store_reg<ModeARM>(reg_rd, it.rd());

    emit_mov_imm<aluop, flg>(rd, it.rot4(), it.imm8());

    const u8 condition = it.cond();        // TODO remove this
    if (flg == SetFlags) {
      arm_complete_store_reg_pc_flags(reg_rd, it.rd());
    } else {
      arm_complete_store_reg_pc_no_flags(reg_rd, it.rd());
    }
  }

  // 3 regs (with op2) instructions
  template <ARMOp aluop, FlagOperation flg>
  inline void arm_alureg3(const ARMInst & it) {
    armcg_regnum rd = prepare_store_reg<ModeARM>(reg_rd, it.rd());

    if (it.op2imm()) {
      armcg_regnum rn = prepare_load_reg<ModeARM>(reg_rn, it.rn(), it.pc, 2);
      armcg_regnum rm = prepare_load_reg<ModeARM>(reg_rm, it.rm(), it.pc, 2);

      emit_alu_reg_immshift<aluop, flg>(rd, rn, rm, it.op2smode(), it.op2sa());
    } else {
      armcg_regnum rn = prepare_load_reg<ModeARM>(reg_rn, it.rn(), it.pc, 3);
      armcg_regnum rm = prepare_load_reg<ModeARM>(reg_rm, it.rm(), it.pc, 3);
      armcg_regnum rs = prepare_load_reg<ModeARM>(reg_rs, it.rs(), it.pc, 3);

      emit_alu_reg_regshift<aluop, flg>(rd, rn, rm, it.op2smode(), rs);
    }

    const u8 condition = it.cond();        // TODO remove this
    if (flg == SetFlags) {
      arm_complete_store_reg_pc_flags(reg_rd, it.rd());
    } else {
      arm_complete_store_reg_pc_no_flags(reg_rd, it.rd());
    }
  }

  template <ARMOp aluop, FlagOperation flg>
  inline void arm_alureg1(const ARMInst & it) {
    armcg_regnum rd = prepare_store_reg<ModeARM>(reg_rd, it.rd());
    if (it.op2imm()) {
      armcg_regnum rm = prepare_load_reg<ModeARM>(reg_rm, it.rm(), it.pc, 2);
      emit_mov_reg_immshift<aluop, flg>(rd, rm, it.op2smode(), it.op2sa());
    } else {
      armcg_regnum rm = prepare_load_reg<ModeARM>(reg_rm, it.rm(), it.pc, 3);
      armcg_regnum rs = prepare_load_reg<ModeARM>(reg_rs, it.rs(), it.pc, 3);
      emit_mov_reg_regshift<aluop, flg>(rd, rm, it.op2smode(), rs);
    }

    const u8 condition = it.cond();        // TODO remove this
    if (flg == SetFlags) {
      arm_complete_store_reg_pc_flags(reg_rd, it.rd());
    } else {
      arm_complete_store_reg_pc_no_flags(reg_rd, it.rd());
    }
  }

  // compare/test instructions
  template <ARMOp aluop, FlagOperation c_flag>
  inline void arm_alureg2(const ARMInst & it) {
    if (it.op2imm()) {
      armcg_regnum rn = prepare_load_reg<ModeARM>(reg_rn, it.rn(), it.pc, 2);
      armcg_regnum rm = prepare_load_reg<ModeARM>(reg_rm, it.rm(), it.pc, 2);

      emit_test_reg_immshift<aluop>(rn, rm, it.op2smode(), it.op2sa());
    } else {
      armcg_regnum rn = prepare_load_reg<ModeARM>(reg_rn, it.rn(), it.pc, 3);
      armcg_regnum rm = prepare_load_reg<ModeARM>(reg_rm, it.rm(), it.pc, 3);
      armcg_regnum rs = prepare_load_reg<ModeARM>(reg_rs, it.rs(), it.pc, 3);

      emit_test_reg_regshift<aluop>(rn, rm, it.op2smode(), rs);
    }
  }

  // Performs 32 bit multiplications (rd and rn are swapped)
  template<FlagOperation flg, MulMode mm>
  inline void arm_mul32(const ARMInst &it) {
    armcg_regnum rm = prepare_load_reg<ModeARM>(reg_rm, it.rm(), it.pc, 2);
    armcg_regnum rs = prepare_load_reg<ModeARM>(reg_rs, it.rs(), it.pc, 2);
    armcg_regnum rd = prepare_store_reg<ModeARM>(reg_a2, it.rn());

    if (mm == MulAdd)
      emit_mla<flg>(rd, rm, rs, prepare_load_reg<ModeARM>(reg_rn, it.rd(), it.pc, 2));
    else
      emit_mul<flg>(rd, rm, rs);

    complete_store_reg<ModeARM>(rd, it.rn());
  }

  // Performs 64 bit multiplications
  template<FlagOperation flg, MulMode mm, bool signmul>
  inline void arm_mul64(const ARMInst &it) {
    armcg_regnum rm = prepare_load_reg<ModeARM>(reg_rm, it.rm(), it.pc, 2);
    armcg_regnum rs = prepare_load_reg<ModeARM>(reg_rs, it.rs(), it.pc, 2);
    armcg_regnum rdlo = (mm == MulAdd) ? prepare_load_reg<ModeARM>(reg_a1, it.rdlo(), it.pc, 2)
                                       : prepare_store_reg<ModeARM>(reg_a1, it.rdlo());
    armcg_regnum rdhi = (mm == MulAdd) ? prepare_load_reg<ModeARM>(reg_a2, it.rdhi(), it.pc, 2)
                                       : prepare_store_reg<ModeARM>(reg_a2, it.rdhi());

    if (signmul) {
      if (mm == MulAdd)
        emit_mull<armgc_smlal, flg>(rdlo, rdhi, rm, rs);
      else
        emit_mull<armgc_smull, flg>(rdlo, rdhi, rm, rs);
    } else {
      if (mm == MulAdd)
        emit_mull<armgc_umlal, flg>(rdlo, rdhi, rm, rs);
      else
        emit_mull<armgc_umull, flg>(rdlo, rdhi, rm, rs);
    }

    complete_store_reg<ModeARM>(rdlo, it.rdlo());
    complete_store_reg<ModeARM>(rdhi, it.rdhi());
  }

  // PSR register read
  template<PSReg reg>
  inline void arm_read_psr(const ARMInst &it) {
    armcg_regnum rd = prepare_store_reg<ModeARM>(reg_a0, it.rd());

    if (reg == RegCPSR) {
      load_memreg(rd, REG_CPSR);
      emit_mrs_cpsr(reg_flags);
      emit_alu_imm<OpBic, NoFlags>(rd, rd, lshift_to_immshf(24), 0xF0);
      emit_alu_imm<OpAnd, NoFlags>(reg_flags, reg_flags, lshift_to_immshf(24), 0xF0);
      emit_alu_reg_immshift<OpOrr, NoFlags>(rd, rd, reg_flags);
    } else {
      emit_alu_imm<OpAdd, NoFlags>(reg_a2, reg_base, lshift_to_immshf(2), SPSR_RAM_OFF >> 2);
      emit_ldr_imm(reg_a1, reg_base, CPU_MODE * 4);
      emit_alu_imm<OpAnd, NoFlags>(reg_a1, reg_a1, 0, 0x0F);
      emit_ldr_reg(rd, reg_a2, reg_a1, ShiftLSL, 2);
    }

    complete_store_reg<ModeARM>(rd, it.rd());
  }

  // PSR register write
  template<PSReg reg, OpType opt>
  inline void arm_write_psr(const ARMInst &it) {
    if (opt == OpReg)
      force_load_reg<ModeARM>(reg_a0, it.rm(), it.pc + 8);
    else
      emit_mov_imm<OpMov, NoFlags>(reg_a0, it.rot4(), it.imm8());

    if (reg == RegCPSR) {
      generate_function_far_call(armfn_store_cpsr);
      write32(cpsr_masks[it.field_fc()][0]);
      write32(cpsr_masks[it.field_fc()][1]);
      write32(it.pc);
    } else {
      load_imm32(reg_a1, spsr_masks[it.field_fc()]);
      emit_ldr_imm(reg_a2, reg_base, (CPU_MODE * 4));
      emit_alu_imm<OpAnd, NoFlags>(reg_a2, reg_a2, 0, 0x0F);
      emit_alu_reg_immshift<OpAdd, NoFlags>(armcg_reglr, reg_base, reg_a2, ShiftLSL, 2);
      emit_alu_reg_immshift<OpAnd, NoFlags>(reg_a0, reg_a0, reg_a1);
      emit_ldr_imm(reg_a2, armcg_reglr, SPSR_RAM_OFF);
      emit_alu_reg_immshift<OpBic, NoFlags>(reg_a2, reg_a2, reg_a1);
      emit_alu_reg_immshift<OpOrr, NoFlags>(reg_a0, reg_a0, reg_a2);
      emit_str_imm(reg_a0, armcg_reglr, SPSR_RAM_OFF);
    }
  }

  template <CPUInstMode cm>
  void trace_instruction(u32 pc, u32 opcode) {
    #ifdef TRACE_INSTRUCTIONS
    for (unsigned i = 0; i < 15; i++)
      if (reg_alloc[cm][i] != mem_reg)
        emit_str_imm(reg_alloc[cm][i], reg_base, i*4);
    emit_mrs_cpsr(reg_flags);
    emit_stmdb(armcg_regsp, 0x500C);
    load_imm32(reg_a0, pc);
    load_imm32(reg_a1, opcode);
    if (cm == ModeThumb) {
      generate_function_far_call(armfn_debug_trace_thumb);
    } else {
      generate_function_far_call(armfn_debug_trace_arm);
    }
    emit_ldmia(armcg_regsp, 0x500C);
    emit_msr_cpsr(reg_flags, armgc_psr_f);
    #endif
  }

  void emit_stubs() {
    rom_cache_watermark = INITIAL_ROM_WATERMARK;
  }

};


void init_emitter(bool must_swap) {
  // Generate handler table
  memcpy(st_lookup_tables, st_handler_functions, sizeof(st_lookup_tables));
  // Issue faster paths if swapping is not required
  if (must_swap)
    memcpy(ld_lookup_tables, ld_swap_handler_functions, sizeof(ld_lookup_tables));
  else
    memcpy(ld_lookup_tables, ld_handler_functions, sizeof(ld_lookup_tables));

  // Emit at the cache base
  CodeEmitter ce(rom_translation_cache, 0);
  ce.emit_stubs();

  // Ensure rom flushes do not wipe this area
  rom_cache_watermark = (u32)(ce.emit_ptr - rom_translation_cache);

  // Now generate BIOS hooks
  init_bios_hooks();

  // Intialize function table
  reg[REG_USERDEF + armfn_gbaup_idle_arm]   = (u32)arm_update_gba_idle_arm;
  reg[REG_USERDEF + armfn_gbaup_idle_thumb] = (u32)arm_update_gba_idle_thumb;
  reg[REG_USERDEF + armfn_gbaup_arm]   = (u32)arm_update_gba_arm;
  reg[REG_USERDEF + armfn_gbaup_thumb] = (u32)arm_update_gba_thumb;
  reg[REG_USERDEF + armfn_swi_arm]   = (u32)execute_swi_arm;
  reg[REG_USERDEF + armfn_swi_thumb] = (u32)execute_swi_thumb;
  reg[REG_USERDEF + armfn_cheat_arm]   = (u32)arm_cheat_hook;
  reg[REG_USERDEF + armfn_cheat_thumb] = (u32)thumb_cheat_hook;
  reg[REG_USERDEF + armfn_store_cpsr]   = (u32)execute_store_cpsr;
  reg[REG_USERDEF + armfn_spsr_restore] = (u32)execute_spsr_restore;
  reg[REG_USERDEF + armfn_indirect_arm]   = (u32)arm_indirect_branch_arm;
  reg[REG_USERDEF + armfn_indirect_thumb] = (u32)arm_indirect_branch_thumb;
  reg[REG_USERDEF + armfn_indirect_dual_arm]   = (u32)arm_indirect_branch_dual_arm;
  reg[REG_USERDEF + armfn_indirect_dual_thumb] = (u32)arm_indirect_branch_dual_thumb;
  reg[REG_USERDEF + armfn_swi6_emu] = (u32)div_emu_sw6;
  reg[REG_USERDEF + armfn_swi7_emu] = (u32)div_emu_sw7;
  reg[REG_USERDEF + armfn_debug_trace_arm] = (u32)trace_instruction_hook_arm;
  reg[REG_USERDEF + armfn_debug_trace_thumb] = (u32)trace_instruction_hook_thumb;
}

u32 execute_arm_translate(u32 cycles) {
  return execute_arm_translate_internal(cycles, &reg[0]);
}

#endif
