/* gameplaySP
 *
 * Copyright (C) 2006 Exophase <exophase@gmail.com>
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

#include "arm_codegen.h"
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
#define armfn_debug_trace_arm     14
#define armfn_debug_trace_thumb   15

#define STORE_TBL_OFF     0x118
#define SPSR_RAM_OFF      0x100

#define write32(value)                                                        \
  *((u32 *)this->emit_ptr) = value;                                           \
  this->emit_ptr += 4                                                         \

#define arm_relative_offset(source, offset)                                   \
  (((((u32)offset - (u32)source) - 8) >> 2) & 0xFFFFFF)                       \


#define reg_a0          ARMREG_R0
#define reg_a1          ARMREG_R1
#define reg_a2          ARMREG_R2

/* scratch0 is shared with flags, be careful! */
#define reg_s0          ARMREG_R9
#define reg_base        ARMREG_R11
#define reg_flags       ARMREG_R9

#define reg_cycles      ARMREG_R12

#define reg_rv          ARMREG_R0

#define reg_rm          ARMREG_R0
#define reg_rn          ARMREG_R1
#define reg_rs          ARMREG_R14
#define reg_rd          ARMREG_R0


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

#define reg_x0         ARMREG_R3
#define reg_x1         ARMREG_R4
#define reg_x2         ARMREG_R5
#define reg_x3         ARMREG_R6
#define reg_x4         ARMREG_R7
#define reg_x5         ARMREG_R8

#define mem_reg        (~0U)

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

u32 arm_register_allocation[] =
{
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

  mem_reg,
  mem_reg,
  mem_reg,
  mem_reg,
  mem_reg,
  mem_reg,
  mem_reg,
  mem_reg,
  mem_reg,
  mem_reg,
  mem_reg,
  mem_reg,
  mem_reg,
  mem_reg,
  mem_reg,
  mem_reg,
};

u32 thumb_register_allocation[] =
{
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

  mem_reg,
  mem_reg,
  mem_reg,
  mem_reg,
  mem_reg,
  mem_reg,
  mem_reg,
  mem_reg,
  mem_reg,
  mem_reg,
  mem_reg,
  mem_reg,
  mem_reg,
  mem_reg,
  mem_reg,
  mem_reg,
};

#define lshift_to_immshf(sa)   ((32 - sa) >> 1)

#define arm_imm_lsl_to_rot(value)                                             \
  (32 - value)                                                                \

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

#if __ARM_ARCH >= 7
  #define arm_load_imm_32bit(ireg, imm)                                       \
  {                                                                           \
    ARM_MOVW(0, ireg, (imm));                                                 \
    if ((imm) >> 16) {                                                        \
      ARM_MOVT(0, ireg, ((imm) >> 16));                                       \
    }                                                                         \
  }
#else
  #define arm_load_imm_32bit(ireg, imm)                                       \
  {                                                                           \
    u32 stores[4];                                                            \
    u32 rotations[4];                                                         \
    u32 store_count = arm_disect_imm_32bit(imm, stores, rotations);           \
    u32 i;                                                                    \
                                                                              \
    ARM_MOV_REG_IMM(0, ireg, stores[0], rotations[0]);                        \
                                                                              \
    for(i = 1; i < store_count; i++)                                          \
    {                                                                         \
      ARM_ORR_REG_IMM(0, ireg, ireg, stores[i], rotations[i]);                \
    }                                                                         \
  }
#endif


#define generate_load_pc(ireg, new_pc)                                        \
  arm_load_imm_32bit(ireg, (new_pc))                                          \

#define generate_load_imm(ireg, imm, imm_ror)                                 \
  ARM_MOV_REG_IMM(0, ireg, imm, imm_ror)                                      \

#define generate_add_imm(ireg, imm, imm_ror)                                  \
  ARM_ADD_REG_IMM(0, ireg, ireg, imm, imm_ror)                                \

#define generate_addsubi(dreg, sreg, imm255)                                  \
  if ((s32)(imm255) >= 0) {                                                   \
    ARM_ADD_REG_IMM(0, (dreg), (sreg), (imm255), 0);                          \
  } else {                                                                    \
    ARM_SUB_REG_IMM(0, (dreg), (sreg), (-(imm255)), 0);                       \
  }                                                                           \

#define generate_add_reg_reg_imm(ireg_dest, ireg_src, imm, imm_ror)           \
  ARM_ADD_REG_IMM(0, ireg_dest, ireg_src, imm, imm_ror)                       \

#define generate_mov(ireg_dest, ireg_src)                                     \
  if(ireg_dest != ireg_src)                                                   \
  {                                                                           \
    ARM_MOV_REG_REG(0, ireg_dest, ireg_src);                                  \
  }                                                                           \

/* Calls functions present in the rom/ram cache (near) */
#define generate_function_call(function_location)                             \
  ARM_BL(0, arm_relative_offset(this->emit_ptr, function_location))           \

/* Calls functions that might be far, via the function table at reg_base */
#define generate_function_far_call(function_number)                           \
  generate_load_memreg(ARMREG_LR, function_number + (u32)REG_USERDEF);        \
  ARM_BLX(0, ARMREG_LR)                                                       \

/* The branch target is to be filled in later (thus a 0 for now) */

#define generate_branch_filler(condition_code, writeback_location)            \
  (writeback_location) = this->emit_ptr;                                      \
  ARM_B_COND(0, condition_code, 0)                                            \

#define generate_update_pc(new_pc)                                            \
  generate_load_pc(reg_a0, new_pc)                                            \

#define generate_cycle_update()                                               \
  if(cycle_count)                                                             \
  {                                                                           \
    if(cycle_count >> 8)                                                      \
    {                                                                         \
      ARM_ADD_REG_IMM(0, reg_cycles, reg_cycles, (cycle_count >> 8) & 0xFF,   \
       arm_imm_lsl_to_rot(8));                                                \
    }                                                                         \
    ARM_ADD_REG_IMM(0, reg_cycles, reg_cycles, (cycle_count & 0xFF), 0);      \
    cycle_count = 0;                                                          \
  }                                                                           \

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
  generate_branch_filler(ARMCOND_AL, writeback_location)                      \

#define generate_branch_update(writeback_location, new_pc, mode)              \
  ARM_MOV_REG_IMMSHIFT(0, reg_a0, reg_cycles, ARMSHIFT_LSR, 31);              \
  /* If counter is negative, skip the update call (2 insts) */                \
  ARM_ADD_REG_IMMSHIFT(0, ARMREG_PC, ARMREG_PC, reg_a0, ARMSHIFT_LSL, 3);     \
  write32(new_pc);                                                            \
  generate_function_far_call(armfn_gbaup_##mode);   /* 2 instructions */      \
  generate_branch_filler(ARMCOND_AL, writeback_location)                      \


#define generate_branch_no_cycle_update(writeback_location, new_pc, mode)     \
  if(pc == idle_loop_target_pc)                                               \
  {                                                                           \
    generate_branch_idle_eliminate(writeback_location, new_pc, mode);         \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    generate_branch_update(writeback_location, new_pc, mode);                 \
  }                                                                           \

#define generate_branch_cycle_update(writeback_location, new_pc, mode)        \
  generate_cycle_update();                                                    \
  generate_branch_no_cycle_update(writeback_location, new_pc, mode)           \

/* a0 holds the destination */

#define generate_indirect_branch_no_cycle_update(type)                        \
  ARM_LDR_IMM(0, ARMREG_PC, reg_base, 4*(REG_USERDEF + armfn_indirect_##type));

#define generate_indirect_branch_cycle_update(type)                           \
  generate_cycle_update();                                                    \
  generate_indirect_branch_no_cycle_update(type)                              \

#define generate_indirect_branch_arm()                                        \
  {                                                                           \
    if(condition == 0x0E)                                                     \
    {                                                                         \
      generate_cycle_update();                                                \
    }                                                                         \
    generate_indirect_branch_no_cycle_update(arm);                            \
  }                                                                           \

#define generate_indirect_branch_dual()                                       \
  {                                                                           \
    if(condition == 0x0E)                                                     \
    {                                                                         \
      generate_cycle_update();                                                \
    }                                                                         \
    generate_indirect_branch_no_cycle_update(dual_arm);                       \
  }                                                                           \

#define arm_generate_store_reg(ireg, reg_index)                               \
{                                                                             \
  u32 store_dest = arm_register_allocation[reg_index];                        \
  if(store_dest != mem_reg)                                                   \
  {                                                                           \
    ARM_MOV_REG_REG(0, store_dest, ireg);                                     \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    ARM_STR_IMM(0, ireg, reg_base, (reg_index * 4));                          \
  }                                                                           \
}                                                                             \

#define thumb_generate_store_reg(ireg, reg_index)                             \
{                                                                             \
  u32 store_dest = thumb_register_allocation[reg_index];                      \
  if(store_dest != mem_reg)                                                   \
  {                                                                           \
    ARM_MOV_REG_REG(0, store_dest, ireg);                                     \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    ARM_STR_IMM(0, ireg, reg_base, (reg_index * 4));                          \
  }                                                                           \
}

#define generate_load_memreg(ireg, reg_index)                                 \
  ARM_LDR_IMM(0, ireg, reg_base, ((reg_index) * 4));                          \

#define arm_generate_load_reg(ireg, reg_index)                                \
{                                                                             \
  u32 load_src = arm_register_allocation[reg_index];                          \
  if(load_src != mem_reg)                                                     \
  {                                                                           \
    ARM_MOV_REG_REG(0, ireg, load_src);                                       \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    ARM_LDR_IMM(0, ireg, reg_base, ((reg_index) * 4));                        \
  }                                                                           \
}                                                                             \

#define thumb_generate_load_reg(ireg, reg_index)                              \
{                                                                             \
  u32 load_src = thumb_register_allocation[reg_index];                        \
  if(load_src != mem_reg)                                                     \
  {                                                                           \
    ARM_MOV_REG_REG(0, ireg, load_src);                                       \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    ARM_LDR_IMM(0, ireg, reg_base, ((reg_index) * 4));                        \
  }                                                                           \
}                                                                             \

#define arm_generate_load_reg_pc(ireg, reg_index, pc_offset)                  \
  if(reg_index == 15)                                                         \
  {                                                                           \
    generate_load_pc(ireg, pc + pc_offset);                                   \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    arm_generate_load_reg(ireg, reg_index);                                   \
  }                                                                           \

#define thumb_generate_load_reg_pc(ireg, reg_index, pc_offset)                \
  if(reg_index == 15)                                                         \
  {                                                                           \
    generate_load_pc(ireg, pc + pc_offset);                                   \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    thumb_generate_load_reg(ireg, reg_index);                                 \
  }                                                                           \

inline u32 arm_prepare_store_reg(u32 scratch_reg, u32 reg_index) {
  u32 reg_use = arm_register_allocation[reg_index];
  if(reg_use == mem_reg)
    return scratch_reg;

  return reg_use;
}

inline u32 thumb_prepare_store_reg(u32 scratch_reg, u32 reg_index) {
  u32 reg_use = thumb_register_allocation[reg_index];
  if(reg_use == mem_reg)
    return scratch_reg;

  return reg_use;
}



#define arm_complete_store_reg(scratch_reg, reg_index)                        \
{                                                                             \
  if(arm_register_allocation[reg_index] == mem_reg)                           \
  {                                                                           \
    ARM_STR_IMM(0, scratch_reg, reg_base, (reg_index * 4));                   \
  }                                                                           \
}

#define thumb_complete_store_reg(scratch_reg, reg_index)                      \
{                                                                             \
  if(thumb_register_allocation[reg_index] == mem_reg)                         \
  {                                                                           \
    ARM_STR_IMM(0, scratch_reg, reg_base, (reg_index * 4));                   \
  }                                                                           \
}

#define arm_complete_store_reg_pc_no_flags(scratch_reg, reg_index)            \
{                                                                             \
  if(reg_index == 15)                                                         \
  {                                                                           \
    generate_indirect_branch_arm();                                           \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    arm_complete_store_reg(scratch_reg, reg_index);                           \
  }                                                                           \
}                                                                             \

#define arm_complete_store_reg_pc_flags(scratch_reg, reg_index)               \
{                                                                             \
  if(reg_index == 15)                                                         \
  {                                                                           \
    if(condition == 0x0E)                                                     \
    {                                                                         \
      generate_cycle_update();                                                \
    }                                                                         \
    generate_function_far_call(armfn_spsr_restore);                           \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    arm_complete_store_reg(scratch_reg, reg_index);                           \
  }                                                                           \
}                                                                             \

/* It should be okay to still generate result flags, spsr will overwrite them.
 * This is pretty infrequent (returning from interrupt handlers, et al) so
 * probably not worth optimizing for.
 */

#define check_for_interrupts()                                                \
  if((io_registers[REG_IE] & io_registers[REG_IF]) &&                         \
   io_registers[REG_IME] && ((reg[REG_CPSR] & 0x80) == 0))                    \
  {                                                                           \
    REG_MODE(MODE_IRQ)[6] = pc + 4;                                           \
    REG_SPSR(MODE_IRQ) = reg[REG_CPSR];                                           \
    reg[REG_CPSR] = 0xD2;                                                     \
    pc = 0x00000018;                                                          \
    set_cpu_mode(MODE_IRQ);                                                   \
  }                                                                           \

#define arm_generate_store_reg_pc_no_flags(ireg, reg_index)                   \
  arm_generate_store_reg(ireg, reg_index);                                    \
  if(reg_index == 15)                                                         \
  {                                                                           \
    generate_indirect_branch_arm();                                           \
  }                                                                           \


u32 execute_spsr_restore_body(u32 pc)
{
  set_cpu_mode(cpu_modes[reg[REG_CPSR] & 0xF]);
  check_for_interrupts();

  return pc;
}

#define generate_save_flags()                                                 \
  ARM_MRS_CPSR(0, reg_flags)                                                  \

#define generate_restore_flags()                                              \
  ARM_MSR_REG(0, ARM_PSR_F, reg_flags, ARM_CPSR)                              \

#define generate_branch(mode)                                                 \
{                                                                             \
  generate_branch_cycle_update(                                               \
   block_exits[block_exit_position].branch_source,                            \
   block_exits[block_exit_position].branch_target, mode);                     \
  block_exit_position++;                                                      \
}                                                                             \


#define generate_op_movs_reg_regshift(_rd, _rn, _rm, shift_type, _rs)         \
  generate_op_reg_regshift_uflags(MOVS, _rd, _rm, shift_type, _rs)            \

#define generate_op_reg_regshift_uflags(name, _rd, _rm, shift_type, _rs)      \
  ARM_##name##_REG_REGSHIFT(0, _rd, _rm, shift_type, _rs)                     \

#define generate_op_reg_immshift_aflags(name, _rd, _rn, _rm, st, shift)       \
  ARM_##name##_REG_IMMSHIFT(0, _rd, _rn, _rm, st, shift)                      \

#define generate_op_reg_immshift_aflags_load_c(name, _rd, _rn, _rm, st, sh)   \
  ARM_##name##_REG_IMMSHIFT(0, _rd, _rn, _rm, st, sh)                         \

#define generate_op_reg_immshift_uflags(name, _rd, _rm, shift_type, shift)    \
  ARM_##name##_REG_IMMSHIFT(0, _rd, _rm, shift_type, shift)                   \

#define generate_op_reg_immshift_tflags(name, _rn, _rm, shift_type, shift)    \
  ARM_##name##_REG_IMMSHIFT(0, _rn, _rm, shift_type, shift)                   \

#define generate_op_subs_reg_immshift(_rd, _rn, _rm, shift_type, shift)       \
  generate_op_reg_immshift_aflags(SUBS, _rd, _rn, _rm, shift_type, shift)     \

#define generate_op_movs_reg_immshift(_rd, _rn, _rm, shift_type, shift)       \
  generate_op_reg_immshift_uflags(MOVS, _rd, _rm, shift_type, shift)          \

#define generate_op_mvns_reg_immshift(_rd, _rn, _rm, shift_type, shift)       \
  generate_op_reg_immshift_uflags(MVNS, _rd, _rm, shift_type, shift)          \

/* The reg operand is in reg_rm, not reg_rn like expected, so rsbs isn't
 * being used here. When rsbs is fully inlined it can be used with the
 * apropriate operands.
 */

#define generate_op_muls_reg_immshift(_rd, _rn, _rm, shift_type, shift)       \
  ARM_MULS(0, _rd, _rn, _rm);                                                 \

// TODO: Get rid of _rd paramenter
#define generate_op_cmp_reg_immshift(_rd, _rn, _rm, shift_type, shift)        \
  generate_op_reg_immshift_tflags(CMP, _rn, _rm, shift_type, shift)           \



void *div6, *divarm7;


/* We use USAT + ROR to map addresses to the handler table. For ARMv5 we use
   the table -1 entry to map any out of range/unaligned access, and some fun
   math/logical tricks to avoid using USAT */

#if __ARM_ARCH >= 6
  #define mem_calc_region(abits)                                              \
    if (abits) {                                                              \
      ARM_MOV_REG_IMMSHIFT(0, reg_a2, reg_a0, ARMSHIFT_ROR, abits)            \
      ARM_USAT_ASR(0, reg_a2, 4, reg_a2, 24-abits, ARMCOND_AL);               \
    } else {                                                                  \
      ARM_USAT_ASR(0, reg_a2, 4, reg_a0, 24, ARMCOND_AL);                     \
    }
#else
  #define mem_calc_region(abits)                                              \
    if (abits) {                                                              \
      ARM_ORR_REG_IMMSHIFT(0, reg_a2, reg_a0, reg_a0, ARMSHIFT_LSL, 32-abits);\
      ARM_MOV_REG_IMMSHIFT(0, reg_a2, reg_a2, ARMSHIFT_LSR, 24);              \
    } else {                                                                  \
      ARM_MOV_REG_IMMSHIFT(0, reg_a2, reg_a0, ARMSHIFT_LSR, 24);              \
    }                                                                         \
    ARM_RSB_REG_IMM(0, ARMREG_LR, reg_a2, 15, 0);                             \
    ARM_ORR_REG_IMMSHIFT(0, reg_a2, reg_a2, ARMREG_LR, ARMSHIFT_ASR, 31);
#endif

#define generate_load_call(tblnum, abits)                                     \
  mem_calc_region(abits);                                                     \
  generate_add_imm(reg_a2, (STORE_TBL_OFF + 68*tblnum + 4) >> 2, 0);          \
  ARM_LDR_REG_REG_SHIFT(0, reg_a2, reg_base, reg_a2, 0, 2);                   \
  ARM_BLX(0, reg_a2);                                                         \

#define generate_store_call(tblnum)                                           \
  mem_calc_region(0);                                                         \
  generate_add_imm(reg_a2, (STORE_TBL_OFF + 68*tblnum + 4) >> 2, 0);          \
  ARM_LDR_REG_REG_SHIFT(0, reg_a2, reg_base, reg_a2, 0, 2);                   \
  ARM_BLX(0, reg_a2);                                                         \


#define generate_store_call_u8()        generate_store_call(0)
#define generate_store_call_u16()       generate_store_call(1)
#define generate_store_call_u32()       generate_store_call(2)
#define generate_store_call_u32_safe()  generate_store_call(3)
#define generate_load_call_u8()         generate_load_call(4, 0)
#define generate_load_call_s8()         generate_load_call(5, 0)
#define generate_load_call_u16()        generate_load_call(6, 1)
#define generate_load_call_s16()        generate_load_call(7, 1)
#define generate_load_call_u32()        generate_load_call(8, 2)


#define complete_store_reg_pc_thumb()                                         \
  if (it.rd_hi() == REG_PC)                                                   \
  {                                                                           \
    generate_indirect_branch_cycle_update(thumb);                             \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    thumb_complete_store_reg(rd, it.rd_hi());                                 \
  }                                                                           \


class CodeEmitter : public ARMEmitter {
public:
  CodeEmitter(u8 *emit_ptr, u8 *emit_end, u32 pc)
   : ARMEmitter(emit_ptr, emit_end) {}

  static unsigned block_prologue_size() { return 0; }
  inline void emit_block_prologue() {}


  inline u32 arm_prepare_load_reg(u32 scratch_reg, u32 reg_index) {
    u32 reg_use = arm_register_allocation[reg_index];
    if(reg_use != mem_reg)
      return reg_use;

    ARM_LDR_IMM(0, scratch_reg, reg_base, (reg_index * 4));
    return scratch_reg;
  }

  inline u32 arm_prepare_load_reg_pc(u32 scratch_reg, u32 reg_index, u32 pc_value) {
    if (reg_index != REG_PC)
      return arm_prepare_load_reg(scratch_reg, reg_index);

    generate_load_pc(scratch_reg, pc_value);
    return scratch_reg;
  }

  inline u32 thumb_prepare_load_reg(u32 scratch_reg, u32 reg_index) {
    u32 reg_use = thumb_register_allocation[reg_index];
    if(reg_use != mem_reg)
      return reg_use;

    ARM_LDR_IMM(0, scratch_reg, reg_base, (reg_index * 4));
    return scratch_reg;
  }

  // Register loading/allocation
  inline u32 thumb_prepare_load_reg_pc(u32 scratch_reg, u32 reg_index, u32 pc_value) {
    if (reg_index != REG_PC)
      return thumb_prepare_load_reg(scratch_reg, reg_index);

    generate_load_pc(scratch_reg, pc_value);
    return scratch_reg;
  }

  // Forces a register load!
  inline void thumb_force_load_reg(u32 dest_reg, u32 reg_index, u32 pc_value) {
    u32 regn = thumb_register_allocation[reg_index];
    if (regn != mem_reg) {
      ARM_MOV_REG_REG(0, dest_reg, regn);
    } else {
      ARM_LDR_IMM(0, dest_reg, reg_base, (reg_index * 4));
    }
  }

  // Forces a register load!
  inline void arm_force_load_reg(u32 dest_reg, u32 reg_index, u32 pc_value) {
    if (reg_index == REG_PC) {
      generate_load_pc(dest_reg, pc_value);
    } else {
      u32 regn = arm_register_allocation[reg_index];
      if (regn != mem_reg) {
        ARM_MOV_REG_REG(0, dest_reg, regn);
      } else {
        ARM_LDR_IMM(0, dest_reg, reg_base, (reg_index * 4));
      }
    }
  }

  template <CPUInstMode cm>
  inline void generate_translation_gate(u32 pc) {
    generate_update_pc(pc);
    if (cm == ModeARM) {
      ARM_LDR_IMM(0, ARMREG_PC, reg_base, 4*(REG_USERDEF + armfn_indirect_arm));
    } else {
      ARM_LDR_IMM(0, ARMREG_PC, reg_base, 4*(REG_USERDEF + armfn_indirect_thumb));
    }
  }

  inline void emit_cycle_update(u32 & cycle_count) {
    generate_cycle_update();
  }

  template <CPUInstMode cm>
  inline void emit_cheat_hook() {
    if (cm == ModeARM) {
      generate_function_far_call(armfn_cheat_arm);
    } else {
      generate_function_far_call(armfn_cheat_thumb);
    }
  }

  inline void emit_load_const_pool(u32 regn, u32 value) {
    u32 rgdst = thumb_prepare_store_reg(reg_a0, regn);
    arm_load_imm_32bit(rgdst, (value));
    thumb_complete_store_reg(rgdst, regn)
  }

  inline void arm_conditional_block_header(u32 condition, u32 & cycle_count, u8 * & backpatch_address) {
    generate_cycle_update();
    /* This will choose the opposite condition */
    condition ^= 0x01;
    generate_branch_filler(condition, backpatch_address);
  }


  // Thumb instruction set
  template <ARMOp aluop>
  inline void thumb_aluop3(const ThumbInst & it) {
    u32 rs = thumb_prepare_load_reg(reg_rs, it.rs());
    u32 rn = thumb_prepare_load_reg(reg_rn, it.rn());
    u32 rd = thumb_prepare_store_reg(reg_rd, it.rd());
    emit_alus_reg<aluop>(rd, rs, rn);
    thumb_complete_store_reg(reg_rd, it.rd());
  }

  template <ARMOp aluop>
  inline void thumb_aluop2(const ThumbInst & it) {
    u32 rs = thumb_prepare_load_reg(reg_rs, it.rs());
    u32 rd = thumb_prepare_load_reg(reg_rd, it.rd());

    if (aluop == OpMul) {
      generate_op_muls_reg_immshift(rd, rd, rs, ARMSHIFT_LSL, 0);
    } else {
      emit_alus_reg<aluop>(rd, rd, rs);
    }

    thumb_complete_store_reg(reg_rd, it.rd());
  }

  template <ARMOp aluop>
  inline void thumb_aluop1(const ThumbInst & it) {
    u32 rs = thumb_prepare_load_reg(reg_rs, it.rs());
    u32 rd = thumb_prepare_store_reg(reg_rd, it.rd());

    switch (aluop) {
    case OpNeg:
      generate_load_imm(reg_rn, 0, 0);
      generate_op_subs_reg_immshift(rd, reg_rn, rs, ARMSHIFT_LSL, 0);
      break;
    case OpMvn:
      generate_op_mvns_reg_immshift(rd, rd, rs, ARMSHIFT_LSL, 0);
      break;
    };

    thumb_complete_store_reg(reg_rd, it.rd());
  }

  template <OpType stype, ShiftType st>
  inline void thumb_shft(const ThumbInst & it) {
    u32 rd = thumb_prepare_store_reg(reg_rd, it.rd());
    u32 rs = thumb_prepare_load_reg(reg_rs, it.rs());

    const u32 shtype = (st == ShiftLSL) ? ARMSHIFT_LSL :
                       (st == ShiftLSR) ? ARMSHIFT_LSR :
                       (st == ShiftASR) ? ARMSHIFT_ASR : ARMSHIFT_ROR;

    if (stype == OpImm) {
      generate_op_movs_reg_immshift(rd, 0, rs, shtype, it.imm5());
    } else {
      u32 rm = thumb_prepare_load_reg(reg_rd, it.rd());
      generate_op_movs_reg_regshift(rd, 0, rm, shtype, rs);
    }

    thumb_complete_store_reg(rd, it.rd());
  }

  template <ARMOp aluop>
  inline void thumb_aluimm2(const ThumbInst & it) {
    switch (aluop) {
    case OpMov:
      {
        u32 rd = thumb_prepare_store_reg(reg_rd, it.rd8());
        ARM_MOVS_REG_IMM(0, rd, it.imm8(), 0);
        thumb_complete_store_reg(reg_rd, it.rd8());
      }
      break;
    case OpAdd:
    case OpSub:
      {
        u32 rd = thumb_prepare_load_reg(reg_rd, it.rd8());
        emit_alus_imm<aluop>(rd, rd, it.imm8());
        thumb_complete_store_reg(reg_rd, it.rd8());
      }
      break;
    case OpCmp:
      {
        u32 rd = thumb_prepare_load_reg(reg_rd, it.rd8());
        ARM_CMP_REG_IMM(0, rd, it.imm8(), 0);
      }
      break;
    };
  }

  template <ARMOp aluop>
  inline void thumb_aluimm3(const ThumbInst & it) {
    u32 rs = thumb_prepare_load_reg(reg_rs, it.rs());
    u32 rd = thumb_prepare_store_reg(reg_rd, it.rd());
    emit_alus_imm<aluop>(rd, rs, it.imm3());
    thumb_complete_store_reg(reg_rd, it.rd());
  }

  template <ARMOp testop>
  inline void thumb_testop(const ThumbInst & it) {
    u32 rs = thumb_prepare_load_reg(reg_rs, it.rs());
    u32 rd = thumb_prepare_load_reg(reg_rd, it.rd());
    emit_test_reg_immshift<testop>(rd, rs, ShiftLSL, 0);
  }

  template <ARMOp aluop>
  inline void thumb_aluhi(const ThumbInst & it, u32 & cycle_count) {
    u32 rs = thumb_prepare_load_reg_pc(reg_rn, it.rs_hi(), it.pc + 4);

    if (aluop == OpAdd) {
      u32 rd = thumb_prepare_load_reg_pc(reg_rd, it.rd_hi(), it.pc + 4);
      emit_alu_reg_immshift<OpAdd, NoFlags>(rd, rd, rs, ShiftLSL, 0);
      complete_store_reg_pc_thumb();
    } else if (aluop == OpCmp) {
      u32 rd = thumb_prepare_load_reg_pc(reg_rd, it.rd_hi(), it.pc + 4);
      generate_op_cmp_reg_immshift(0, rd, rs, ARMSHIFT_LSL, 0);
    } else if (aluop == OpMov) {
      u32 rd = thumb_prepare_store_reg(reg_rd, it.rd_hi());
      ARM_MOV_REG_REG(0, rd, rs);
      complete_store_reg_pc_thumb();
    }
  }

  template <u32 ref_reg>
  inline void thumb_regoff(const ThumbInst & it) {
    if (ref_reg == REG_PC) {
      u32 rd = thumb_prepare_store_reg(reg_rd, it.rd8());
      generate_load_pc(rd, (it.pc & ~2) + 4 + 4 * it.imm8());
      thumb_complete_store_reg(reg_rd, it.rd8());
    } else {
      u32 sreg = thumb_prepare_load_reg(reg_a0, ref_reg);
      u32 rd = thumb_prepare_store_reg(reg_rd, it.rd8());
      ARM_ADD_REG_IMM(0, rd, sreg, it.imm8(), arm_imm_lsl_to_rot(2));  /* Scaled by 4 */
      thumb_complete_store_reg(reg_rd, it.rd8());
    }
  }

  inline void thumb_spadj(s8 offset) {
    u32 sp = thumb_prepare_load_reg(reg_a0, REG_SP);
    if (offset >= 0)
      emit_alu_imm<OpAdd, NoFlags>(sp, sp, lshift_to_immshf(2), offset);
    else
      emit_alu_imm<OpSub, NoFlags>(sp, sp, lshift_to_immshf(2), -offset);
    thumb_complete_store_reg(reg_a0, REG_SP);
  }

  inline void thumb_bx(u32 pc, u32 regn, u32 & cycle_count) {
    thumb_generate_load_reg_pc(reg_a0, regn, 4);
    generate_indirect_branch_cycle_update(dual_thumb);
  }

  inline void arm_bx(const ARMInst & it, u32 & cycle_count) {
    const u8 condition = it.cond();        // TODO remove this
    arm_force_load_reg(reg_a0, it.rm(), it.pc + 8);
    generate_indirect_branch_dual();
  }

  inline bool thumb_emu_swi(u32 pc, u32 num, u32 & cycle_count) {
    switch (num) {
    case 6:
      cycle_count += 64;
      cycle_count += 11 + 32;    // TODO just 64 cycles like other archs.
      generate_function_call(div6);
      return true;
    case 7:
      cycle_count += 64;
      cycle_count += 14 + 32;    // TODO just 64 cycles like other archs.
      generate_function_call(divarm7);
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

    generate_function_far_call(armfn_swi_thumb);
    write32((pc + 2));
    generate_branch_cycle_update(brtgt, 0x00000008, arm);

    return brtgt;
  }

  inline u8* arm_swi(u32 pc, u32 & cycle_count) {
    u8 *brtgt = NULL;

    generate_function_far_call(armfn_swi_arm);
    write32((pc + 4));
    generate_branch_cycle_update(brtgt, 0x00000008, arm);

    return brtgt;
  }

  template <ARMCondCode ccode>
  inline u8* thumb_brcond(u32 pc, u32 target, u32 & cycle_count) {
    u8 *brtgt = NULL;
    u8 *ptch = NULL;

    u32 oppcode = (ccode ^ 0x01);   // Simple opposite code conversion!

    generate_cycle_update();
    generate_branch_filler(oppcode, ptch);
    generate_branch_no_cycle_update(brtgt, target, thumb);
    generate_branch_patch_conditional(ptch, this->emit_ptr);
    return brtgt;
  }

  inline u8* thumb_b(u32 pc, u32 target, u32 & cycle_count) {
    u8 *brtgt = NULL;
    generate_branch_cycle_update(brtgt, target, thumb);
    return brtgt;
  }

  inline u8* arm_b(const ARMInst & it, u32 target, u32 & cycle_count) {
    const u32 pc = it.pc;  // TODO: Remove this
    u8 *brtgt = NULL;
    if (it.cond() == CondAL) {
      generate_branch_cycle_update(brtgt, target, arm);
    } else {
      generate_branch_no_cycle_update(brtgt, target, arm);
    }
    return brtgt;
  }

  inline u8* thumb_bl(u32 pc, u32 target, u32 & cycle_count) {
    u8 *brtgt = NULL;
    generate_update_pc(((pc + 2) | 0x01));
    thumb_generate_store_reg(reg_a0, REG_LR);
    generate_branch_cycle_update(brtgt, target, thumb);
    return brtgt;
  }

  inline u8* arm_bl(const ARMInst & it, u32 target, u32 & cycle_count) {
    const u32 pc = it.pc;  // TODO: Remove this
    u8 *brtgt = NULL;
    generate_update_pc(pc + 4);
    arm_generate_store_reg(reg_a0, REG_LR);
    if (it.cond() == CondAL) {
      generate_branch_cycle_update(brtgt, target, arm);
    } else {
      generate_branch_no_cycle_update(brtgt, target, arm);
    }
    return brtgt;
  }

  inline void thumb_blh(u32 pc, u32 offset, u32 & cycle_count) {
    u32 offlo = (offset) & 0xFF;
    u32 offhi = (offset) >> 8;

    generate_update_pc(((pc + 2) | 0x01));
    thumb_generate_load_reg(reg_a1, REG_LR);
    thumb_generate_store_reg(reg_a0, REG_LR);
    generate_add_reg_reg_imm(reg_a0, reg_a1, offlo, 0);
    if (offhi) {
      generate_add_reg_reg_imm(reg_a0, reg_a0, offhi, arm_imm_lsl_to_rot(8));
    }
    generate_indirect_branch_cycle_update(thumb);
  }

  // ============= Memory functions =================
  template <typename memtype, ThumbMemOffset offt>
  inline void thumb_memaddr(const ThumbInst & it, u32 regn) {
    // Generate the memory address to a0
    if (offt == OffPC) {
      // PC-relative offset. It is word aligned.
      generate_load_pc(reg_a0, ((it.pc & (~3U)) + it.imm8() * 4 + 4));
    } else {
      u32 rb = thumb_prepare_load_reg(reg_a0, regn);
      if (offt == OffReg) {
        u32 ro = thumb_prepare_load_reg(reg_a1, it.ro());
        ARM_ADD_REG_REG(0, reg_a0, rb, ro);
      } else if (offt == OffImm5) {
        ARM_ADD_REG_IMM(0, reg_a0, rb, (it.imm5() * sizeof(memtype)), 0);
      } else {
        u32 rotam = sizeof(memtype) / 2;  // log2(size)
        ARM_ADD_REG_IMM(0, reg_a0, rb, it.imm8(), arm_imm_lsl_to_rot(rotam));
      }
    }
  }

  template <typename memtype, ThumbMemOffset offt>
  inline void thumb_memld(const ThumbInst & it, u32 regd, u32 regn, u32 & cycle_count) {
    cycle_count += 2;  // TODO: Use proper cycle accounting and honor WAITCNT
    // Generate the address
    thumb_memaddr<memtype, offt>(it, regn);
    // Generate a call to the right memory section handler.
    u32 ldtype = ldr_handler_offset<memtype>();
    u32 nbits = sizeof(memtype) / 2;  // log2(size)
    mem_calc_region(nbits);
    generate_add_imm(reg_a2, (STORE_TBL_OFF + 68*ldtype + 4) >> 2, 0);
    ARM_LDR_REG_REG_SHIFT(0, reg_a2, reg_base, reg_a2, 0, 2);
    ARM_BLX(0, reg_a2);
    write32(it.pc);
    thumb_generate_store_reg(reg_rv, regd);
  }

  template <typename memtype, ThumbMemOffset offt>
  inline void thumb_memst(const ThumbInst & it, u32 regd, u32 regn, u32 & cycle_count) {
    cycle_count++;  // TODO: Use proper cycle accounting and honor WAITCNT
    // Generate the address
    thumb_memaddr<memtype, offt>(it, regn);
    // Load value and generate call to handler
    u32 sttype = str_handler_offset<memtype>();
    mem_calc_region(0);
    generate_add_imm(reg_a2, (STORE_TBL_OFF + 68*sttype + 4) >> 2, 0);
    ARM_LDR_REG_REG_SHIFT(0, reg_a2, reg_base, reg_a2, 0, 2);
    thumb_generate_load_reg(reg_a1, regd);
    ARM_BLX(0, reg_a2);
    write32((it.pc + 2));
  }


  template <ARMMemOffset offt, MemOffDir dir>
  inline void arm_memaddr(u32 oreg, const ARMInst & it) {
    // Load base register if needed
    u32 breg = arm_prepare_load_reg_pc(oreg, it.rn(), it.pc + 8);
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
        u32 secreg = arm_prepare_load_reg_pc(reg_a2, it.rm(), it.pc + 8);
        emit_alu_reg_immshift<aop, NoFlags>(oreg, breg, secreg, ShiftLSL, 0);
      }
      break;
    case OffOp2Reg:    // [rn +/- rm shift/rot amount]
      {
        u32 secreg = arm_prepare_load_reg_pc(reg_a2, it.rm(), it.pc + 8);
        emit_alu_reg_immshift<aop, NoFlags>(oreg, breg, secreg, it.op2smode(), it.op2sa());
      }
      break;
    };
  }

  template <typename memtype, ARMMemOffset offt, MemOffDir dir, MemIdxMode idxm>
  inline void arm_memst(const ARMInst & it, u32 & cycle_count) {
    cycle_count++;    // TODO: Use proper cycle accounting and honor WAITCNT

    // Generate the final address and base address, and write back if necessary
    if (idxm == MemIdxPostWB) {
      // Load the base reg to a0
      arm_force_load_reg(reg_a0, it.rn(), it.pc + 4);
      // Calculate the final value to the final reg.
      u32 wbreg = arm_prepare_store_reg(reg_a1, it.rn());
      arm_memaddr<offt, dir>(wbreg, it);
      arm_complete_store_reg(wbreg, it.rn());
    }
    else {
      arm_memaddr<offt, dir>(reg_a0, it);  // Calculate final addr to a0
      if (idxm == MemIdxPreWB) {
        arm_generate_store_reg(reg_a0, it.rn());
      }
    }

    // Generate call to handler, load the value to write to a1
    arm_force_load_reg(reg_a1, it.rd(), it.pc + 12);
    generate_store_call(str_handler_offset<memtype>());
    write32((it.pc + 4));
  }

  template <typename memtype, ARMMemOffset offt, MemOffDir dir, MemIdxMode idxm>
  inline void arm_memld(const ARMInst & it, u32 & cycle_count) {
    const u8 condition = it.cond();        // TODO remove this
    cycle_count += 2;    // TODO: Use proper cycle accounting and honor WAITCNT

    // Generate the final address and base address, and write back if necessary
    if (idxm == MemIdxPostWB) {
      // Load the base reg to a0
      arm_force_load_reg(reg_a0, it.rn(), it.pc + 4);
      // Calculate the final value to the final reg.
      u32 wbreg = arm_prepare_store_reg(reg_a1, it.rn());
      arm_memaddr<offt, dir>(wbreg, it);
      arm_complete_store_reg(wbreg, it.rn());
    }
    else {
      arm_memaddr<offt, dir>(reg_a0, it);  // Calculate final addr to a0
      if (idxm == MemIdxPreWB) {
        arm_generate_store_reg(reg_a0, it.rn());
      }
    }

    // Generate call to handler, load the value to write to a1
    generate_store_call(ldr_handler_offset<memtype>());
    write32(it.pc);
    arm_generate_store_reg_pc_no_flags(reg_rv, it.rd());
  }

  template <typename memtype>
  inline void arm_swap(const ARMInst & it, u32 & cycle_count) {
    cycle_count += 3;   // TODO: Some more accurate accounting :)

    // rd = mem[rn], mem[rn] = rm (Note: all regs could be the same!)

    arm_force_load_reg(reg_a0, it.rn(), it.pc + 4);
    generate_store_call(ldr_handler_offset<memtype>());
    write32(it.pc);

    generate_mov(reg_a2, reg_rv);
    arm_force_load_reg(reg_a0, it.rn(), it.pc + 4);
    arm_force_load_reg(reg_a1, it.rm(), it.pc + 4);
    arm_generate_store_reg(reg_a2, it.rd());
    generate_store_call(str_handler_offset<memtype>());
    write32((it.pc + 4));
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

    // Load base register, clear its lower bits.
    u32 nreg = (cpum == ModeThumb) ? thumb_prepare_load_reg_pc(reg_a1, basereg, pc + 4) :
                                     arm_prepare_load_reg_pc(reg_a1, basereg, pc + 8);
    ARM_BIC_REG_IMM(0, reg_a0, nreg, 0x03, 0);
    arm_generate_store_reg(reg_a0, REG_SAVE);   // TODO: Eliminate stores to "extended" regsiters

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
      if (cpum == ModeThumb) {
        u32 scratch = thumb_prepare_store_reg(reg_a2, basereg);
        generate_addsubi(scratch, nreg, endoff);
        thumb_generate_store_reg(scratch, basereg);
      } else {
        u32 scratch = arm_prepare_store_reg(reg_a2, basereg);
        generate_addsubi(scratch, nreg, endoff);
        arm_generate_store_reg(scratch, basereg);
      }
    }

    u32 aoff = 0;
    for (u32 i = 0; i < 16; i++) {
      if (rlist & (1 << i)) {
        thumb_generate_load_reg(reg_a0, REG_SAVE);
        generate_addsubi(reg_a0, reg_a0, (aoff + inioff));
        if (amode == AccLoad) {
          u32 ldtype = ldr_handler_offset<u32>();
          mem_calc_region(0);
          generate_add_imm(reg_a2, (STORE_TBL_OFF + 68*ldtype + 4) >> 2, 0);
          ARM_LDR_REG_REG_SHIFT(0, reg_a2, reg_base, reg_a2, 0, 2);
          ARM_BLX(0, reg_a2);
          write32(pc + itsize);
          if (cpum == ModeThumb) {
            thumb_generate_store_reg(reg_rv, i);
          } else {
            arm_generate_store_reg(reg_rv, i);
          }
        } else {
          if (cpum == ModeThumb) {
            thumb_generate_load_reg(reg_a1, i);
          } else {
            arm_generate_load_reg_pc(reg_a1, i, pc + 12);
          }

          // Update the base register right after the first read if necessary
          if (writeback && !writeback_first) {
            if (cpum == ModeThumb) {
              u32 scratch = thumb_prepare_load_reg_pc(reg_a2, basereg, pc + 4);
              generate_addsubi(scratch, scratch, endoff);
              thumb_generate_store_reg(scratch, basereg);
            } else {
              u32 scratch = arm_prepare_load_reg_pc(reg_a2, basereg, pc + 8);
              generate_addsubi(scratch, scratch, endoff);
              arm_generate_store_reg(scratch, basereg);
            }
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


  // ======== ARM instructions ======================================
  template <ARMOp aluop, FlagOperation flg>
  inline void arm_aluimm3(const ARMInst & it, u32 & cycle_count) {
    u32 rn = arm_prepare_load_reg_pc(reg_rn, it.rn(), it.pc + 8);
    u32 rd = arm_prepare_store_reg(reg_rd, it.rd());

    emit_alu_imm<aluop, flg>(rd, rn, it.rot4(), it.imm8());

    const u8 condition = it.cond();        // TODO remove this
    if (flg == SetFlags) {
      arm_complete_store_reg_pc_flags(reg_rd, it.rd());
    } else {
      arm_complete_store_reg_pc_no_flags(reg_rd, it.rd());
    }
  }

  template <ARMOp aluop>
  inline void arm_aluimm2(const ARMInst & it, u32 & cycle_count) {
    u32 rn = arm_prepare_load_reg_pc(reg_rn, it.rn(), it.pc + 8);
    emit_test_imm<aluop>(rn, it.rot4(), it.imm8());
  }

  template <ARMOp aluop, FlagOperation flg>
  inline void arm_aluimm1(const ARMInst & it, u32 & cycle_count) {
    u32 rd = arm_prepare_store_reg(reg_rd, it.rd());

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
  inline void arm_alureg3(const ARMInst & it, u32 & cycle_count) {
    u32 rd = arm_prepare_store_reg(reg_rd, it.rd());

    if (it.op2imm()) {
      u32 rn = arm_prepare_load_reg_pc(reg_rn, it.rn(), it.pc + 8);
      u32 rm = arm_prepare_load_reg_pc(reg_rm, it.rm(), it.pc + 8);

      emit_alu_reg_immshift<aluop, flg>(rd, rn, rm, it.op2smode(), it.op2sa());
    } else {
      u32 rn = arm_prepare_load_reg_pc(reg_rn, it.rn(), it.pc + 12);
      u32 rm = arm_prepare_load_reg_pc(reg_rm, it.rm(), it.pc + 12);
      u32 rs = arm_prepare_load_reg_pc(reg_rs, it.rs(), it.pc + 12);

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
  inline void arm_alureg1(const ARMInst & it, u32 & cycle_count) {
    u32 rd = arm_prepare_store_reg(reg_rd, it.rd());
    if (it.op2imm()) {
      u32 rm = arm_prepare_load_reg_pc(reg_rm, it.rm(), it.pc + 8);
      emit_mov_reg_immshift<aluop, flg>(rd, rm, it.op2smode(), it.op2sa());
    } else {
      u32 rm = arm_prepare_load_reg_pc(reg_rm, it.rm(), it.pc + 12);
      u32 rs = arm_prepare_load_reg_pc(reg_rs, it.rs(), it.pc + 12);
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
      u32 rn = arm_prepare_load_reg_pc(reg_rn, it.rn(), it.pc + 8);
      u32 rm = arm_prepare_load_reg_pc(reg_rm, it.rm(), it.pc + 8);

      emit_test_reg_immshift<aluop>(rn, rm, it.op2smode(), it.op2sa());
    } else {
      u32 rn = arm_prepare_load_reg_pc(reg_rn, it.rn(), it.pc + 12);
      u32 rm = arm_prepare_load_reg_pc(reg_rm, it.rm(), it.pc + 12);
      u32 rs = arm_prepare_load_reg_pc(reg_rs, it.rs(), it.pc + 12);

      emit_test_reg_regshift<aluop>(rn, rm, it.op2smode(), rs);
    }
  }

  // Performs 32 bit multiplications (rd and rn are swapped)
  template<FlagOperation flg, MulMode mm>
  inline void arm_mul32(const ARMInst &it) {
    u32 rm = arm_prepare_load_reg_pc(reg_rm, it.rm(), it.pc + 8);
    u32 rs = arm_prepare_load_reg_pc(reg_rs, it.rs(), it.pc + 8);
    u32 rd = arm_prepare_store_reg(reg_a2, it.rn());

    if (mm == MulAdd) {
      u32 rn = arm_prepare_load_reg_pc(reg_rn, it.rd(), it.pc + 8);
      if (flg == SetFlags) {
        ARM_MLAS(0, rd, rm, rs, rn);
      } else {
        ARM_MLA(0, rd, rm, rs, rn);
      }
    } else {
      if (flg == SetFlags) {
        ARM_MULS(0, rd, rm, rs);
      } else {
        ARM_MUL(0, rd, rm, rs);
      }
    }

    arm_complete_store_reg(rd, it.rn());
  }

  // Performs 64 bit multiplications
  template<FlagOperation flg, MulMode mm, bool signmul>
  inline void arm_mul64(const ARMInst &it) {
    u32 rm = arm_prepare_load_reg_pc(reg_rm, it.rm(), it.pc + 8);
    u32 rs = arm_prepare_load_reg_pc(reg_rs, it.rs(), it.pc + 8);
    u32 rdlo = (mm == MulAdd) ? arm_prepare_load_reg_pc(reg_a1, it.rdlo(), it.pc + 8)
                              : arm_prepare_store_reg(reg_a1, it.rdlo());
    u32 rdhi = (mm == MulAdd) ? arm_prepare_load_reg_pc(reg_a2, it.rdhi(), it.pc + 8)
                              : arm_prepare_store_reg(reg_a2, it.rdhi());

    if (signmul) {
      if (mm == MulAdd) {
        if (flg == SetFlags) {
          ARM_SMLALS(0, rdlo, rdhi, rm, rs);
        } else {
          ARM_SMLAL(0, rdlo, rdhi, rm, rs);
        }
      } else {
        if (flg == SetFlags) {
          ARM_SMULLS(0, rdlo, rdhi, rm, rs);
        } else {
          ARM_SMULL(0, rdlo, rdhi, rm, rs);
        }
      }
    } else {
      if (mm == MulAdd) {
        if (flg == SetFlags) {
          ARM_UMLALS(0, rdlo, rdhi, rm, rs);
        } else {
          ARM_UMLAL(0, rdlo, rdhi, rm, rs);
        }
      } else {
        if (flg == SetFlags) {
          ARM_UMULLS(0, rdlo, rdhi, rm, rs);
        } else {
          ARM_UMULL(0, rdlo, rdhi, rm, rs);
        }
      }
    }

    arm_complete_store_reg(rdlo, it.rdlo());
    arm_complete_store_reg(rdhi, it.rdhi());
  }

  // PSR register read
  template<PSReg reg>
  inline void arm_read_psr(const ARMInst &it) {
    u32 rd = arm_prepare_store_reg(reg_a0, it.rd());

    if (reg == RegCPSR) {
      generate_load_memreg(rd, REG_CPSR);
      generate_save_flags();
      ARM_BIC_REG_IMM(0, rd, rd, 0xF0, arm_imm_lsl_to_rot(24));
      ARM_AND_REG_IMM(0, reg_flags, reg_flags, 0xF0, arm_imm_lsl_to_rot(24));
      ARM_ORR_REG_REG(0, rd, rd, reg_flags);
    } else {
      ARM_ADD_REG_IMM(0, reg_a2, reg_base, SPSR_RAM_OFF >> 2, 30);
      ARM_LDR_IMM(0, reg_a1, reg_base, CPU_MODE * 4);
      ARM_AND_REG_IMM(0, reg_a1, reg_a1, 0xF, 0);
      ARM_LDR_REG_REG_SHIFT(0, rd, reg_a2, reg_a1, ARMSHIFT_LSL, 2);
    }

    arm_complete_store_reg(rd, it.rd())
  }

  // PSR register write
  template<PSReg reg, OpType opt>
  inline void arm_write_psr(const ARMInst &it) {
    if (opt == OpReg) {
      arm_force_load_reg(reg_a0, it.rm(), it.pc + 8);
    } else {
      generate_load_imm(reg_a0, it.imm8(), it.rot4() * 2);
    }

    if (reg == RegCPSR) {
      generate_function_far_call(armfn_store_cpsr);
      write32(cpsr_masks[it.field_fc()][0]);
      write32(cpsr_masks[it.field_fc()][1]);
      write32(it.pc);
    } else {
      arm_load_imm_32bit(reg_a1, spsr_masks[it.field_fc()]);
      ARM_LDR_IMM(0, reg_a2, reg_base, (CPU_MODE * 4));
      ARM_AND_REG_IMM(0, reg_a2, reg_a2, 0xF, 0);
      ARM_ADD_REG_IMMSHIFT(0, ARMREG_LR, reg_base, reg_a2, ARMSHIFT_LSL, 2);
      ARM_AND_REG_IMMSHIFT(0, reg_a0, reg_a0, reg_a1, ARMSHIFT_LSL, 0);
      ARM_LDR_IMM(0, reg_a2, ARMREG_LR, SPSR_RAM_OFF);
      ARM_BIC_REG_IMMSHIFT(0, reg_a2, reg_a2, reg_a1, ARMSHIFT_LSL, 0);
      ARM_ORR_REG_IMMSHIFT(0, reg_a0, reg_a0, reg_a2, ARMSHIFT_LSL, 0);
      ARM_STR_IMM(0, reg_a0, ARMREG_LR, SPSR_RAM_OFF);
    }
  }

  template <CPUInstMode cm>
  void trace_instruction(u32 pc, u32 opcode) {
    #ifdef TRACE_INSTRUCTIONS
    const u32 *rt = (cm == ModeThumb) ? thumb_register_allocation
                                      : arm_register_allocation;

    for (unsigned i = 0; i < 15; i++) {
      if (rt[i] != mem_reg) {
        ARM_STR_IMM(0, rt[i], reg_base, (i*4));
      }
    }
    generate_save_flags();
    ARM_STMDB_WB(0, ARMREG_SP, 0x500C);
    arm_load_imm_32bit(reg_a0, pc);
    arm_load_imm_32bit(reg_a1, opcode);
    if (cm == ModeThumb) {
      generate_function_far_call(armfn_debug_trace_thumb);
    } else {
      generate_function_far_call(armfn_debug_trace_arm);
    }
    ARM_LDMIA_WB(0, ARMREG_SP, 0x500C);
    generate_restore_flags();
    #endif
  }

  void emit_stubs() {
    rom_cache_watermark = INITIAL_ROM_WATERMARK;

    // Generate ARMv5+ division code, uses a mix of libgcc and some open bioses.
    // This is meant for ARMv5 or higher, uses CLZ

    // Invert operands for SWI 7 (divarm)
    divarm7 = this->emit_ptr;
    ARM_MOV_REG_REG(0, reg_a2, reg_x0);
    ARM_MOV_REG_REG(0, reg_x0, reg_x1);
    ARM_MOV_REG_REG(0, reg_x1, reg_a2);

    div6 = this->emit_ptr;
    // Save flags before using them
    generate_save_flags();
    // Stores result and remainder signs 
    ARM_ANDS_REG_IMM(0, reg_a2, reg_x1, 0x80, arm_imm_lsl_to_rot(24));
    ARM_EOR_REG_IMMSHIFT(0, reg_a2, reg_a2, reg_x0, ARMSHIFT_ASR, 1);

    // Make numbers positive if they are negative
    ARM_RSB_REG_IMM_COND(0, reg_x1, reg_x1, 0, 0, ARMCOND_MI);
    ARM_TST_REG_REG(0, reg_x0, reg_x0);
    ARM_RSB_REG_IMM_COND(0, reg_x0, reg_x0, 0, 0, ARMCOND_MI);

    // Calculates the number of iterations to division, and jumps to unrolled code
    ARM_CLZ(0, reg_a0, reg_x0);
    ARM_CLZ(0, reg_a1, reg_x1);
    ARM_SUBS_REG_REG(0, reg_a0, reg_a1, reg_a0);          // Align and check if a<b
    ARM_RSB_REG_IMM(0, reg_a0, reg_a0, 31, 0);
    ARM_MOV_REG_IMM_COND(0, reg_a0, 32, 0, ARMCOND_MI);   // Cap to 32 (skip division)
    ARM_ADD_REG_IMMSHIFT(0, reg_a0, reg_a0, reg_a0, ARMSHIFT_LSL, 1);
    ARM_MOV_REG_IMM(0, reg_a1, 0, 0);
    ARM_ADD_REG_IMMSHIFT(0, ARMREG_PC, ARMREG_PC, reg_a0, ARMSHIFT_LSL, 2);
    ARM_NOP(0);

    for (int i = 31; i >= 0; i--) {
      ARM_CMP_REG_IMMSHIFT(0, reg_x0, reg_x1, ARMSHIFT_LSL, i);
      ARM_ADC_REG_REG(0, reg_a1, reg_a1, reg_a1);
      ARM_SUB_REG_IMMSHIFT_COND(0, reg_x0, reg_x0, reg_x1, ARMSHIFT_LSL, i, ARMCOND_HS);
    }

    ARM_MOV_REG_REG(0, reg_x1, reg_x0);
    ARM_MOV_REG_REG(0, reg_x0, reg_a1);
    // Negate result if sign is negative
    ARM_SHLS_IMM(0, reg_a2, reg_a2, 1);
    ARM_RSB_REG_IMM_COND(0, reg_x0, reg_x0, 0, 0, ARMCOND_HS);
    ARM_RSB_REG_IMM_COND(0, reg_x1, reg_x1, 0, 0, ARMCOND_MI);

    // Register R3 stores the abs(r0/r1), store it in the right reg/mem-reg
    generate_load_memreg(reg_a2, REG_CPSR);
    ARM_TST_REG_IMM8(0, reg_a2, 0x20);
    arm_generate_store_reg(reg_a1, 3 /* r3 */);
    ARM_MOV_REG_REG_COND(0, reg_x3, reg_a1, ARMCOND_NE);

    // Return and continue regular emulation
    generate_restore_flags();
    ARM_BX(0, ARMREG_LR);
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
  CodeEmitter ce(rom_translation_cache, &rom_translation_cache[ROM_TRANSLATION_CACHE_SIZE], 0);
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
  reg[REG_USERDEF + armfn_debug_trace_arm] = (u32)trace_instruction_hook_arm;
  reg[REG_USERDEF + armfn_debug_trace_thumb] = (u32)trace_instruction_hook_thumb;
}

u32 execute_arm_translate(u32 cycles) {
  return execute_arm_translate_internal(cycles, &reg[0]);
}

#endif
