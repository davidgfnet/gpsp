/* gameplaySP
 *
 * Copyright (C) 2006 Exophase <exophase@gmail.com>
 * Copyright (C) 2024 David Guillen Fandos <david@davidgf.net>
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

#ifndef X86_CODEGEN_H
#define X86_CODEGEN_H

typedef enum {
  x86_reg_eax = 0,
  x86_reg_ecx = 1,
  x86_reg_edx = 2,
  x86_reg_ebx = 3,
  x86_reg_esp = 4,
  x86_reg_ebp = 5,
  x86_reg_esi = 6,
  x86_reg_edi = 7
} x86_regnum;

#define x86_emit_byte(value)                                                  \
  *translation_ptr = value;                                                   \
  translation_ptr++                                                           \

#define x86_emit_dword(value)                                                 \
  *((u32 *)translation_ptr) = value;                                          \
  translation_ptr += 4                                                        \

typedef enum
{
  x86_mod_mem        = 0,
  x86_mod_mem_disp8  = 1,
  x86_mod_mem_disp32 = 2,
  x86_mod_reg        = 3
} x86_mod;

#define x86_emit_mod_rm(mod, rm, spare)                                       \
  x86_emit_byte((mod << 6) | (spare << 3) | rm)                               \

#define x86_emit_sib(scale, ridx, rbase)                                      \
  x86_emit_byte(((scale) << 6) | ((ridx) << 3) | (rbase))                     \

// Memory op: dest = [base + offset]
#define x86_emit_mem_op(dest, base, offset)                                   \
  if(offset == 0)                                                             \
  {                                                                           \
    x86_emit_mod_rm(x86_mod_mem, base, dest);                                 \
  }                                                                           \
  else if(((s32)offset < 127) && ((s32)offset > -128))                        \
  {                                                                           \
    x86_emit_mod_rm(x86_mod_mem_disp8, base, dest);                           \
    x86_emit_byte((s8)offset);                                                \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    x86_emit_mod_rm(x86_mod_mem_disp32, base, dest);                          \
    x86_emit_dword(offset);                                                   \
  }                                                                           \

// Memory op: dest =[base + ridx << scale + offset]
#define x86_emit_mem_sib_op(dest, base, ridx, scale, offset)                  \
  if(offset == 0)                                                             \
  {                                                                           \
    x86_emit_mod_rm(x86_mod_mem, 0x4, dest);                                  \
    x86_emit_sib(scale, ridx, base);                                          \
  }                                                                           \
  else if(((s32)offset < 127) && ((s32)offset > -128))                        \
  {                                                                           \
    x86_emit_mod_rm(x86_mod_mem_disp8, 0x4, dest);                            \
    x86_emit_sib(scale, ridx, base);                                          \
    x86_emit_byte((s8)offset);                                                \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    x86_emit_mod_rm(x86_mod_mem_disp32, 0x4, dest);                           \
    x86_emit_sib(scale, ridx, base);                                          \
    x86_emit_dword(offset);                                                   \
  }                                                                           \

#define x86_emit_reg_op(dest, source)                                         \
  x86_emit_mod_rm(x86_mod_reg, source, dest)                                  \


typedef enum
{
  x86_opcode_mov_rm_reg                 = 0x89,
  x86_opcode_mov_reg_rm                 = 0x8B,
  x86_opcode_mov_reg_imm                = 0xB8,
  x86_opcode_mov_rm_imm                 = 0x00C7,
  x86_opcode_ror_reg_imm                = 0x01C1,
  x86_opcode_shl_reg_imm                = 0x04C1,
  x86_opcode_shr_reg_imm                = 0x05C1,
  x86_opcode_sar_reg_imm                = 0x07C1,
  x86_opcode_ror_reg_rm                 = 0x01D3,
  x86_opcode_rcr_reg_rm                 = 0x03D3,
  x86_opcode_shl_reg_rm                 = 0x04D3,
  x86_opcode_shr_reg_rm                 = 0x05D3,
  x86_opcode_sar_reg_rm                 = 0x07D3,
  x86_opcode_rcr_reg1                   = 0x03D1,
  x86_opcode_call_offset                = 0xE8,
  x86_opcode_ret                        = 0xC3,
  x86_opcode_test_rm_imm                = 0x00F7,
  x86_opcode_test_reg_rm                = 0x85,
  x86_opcode_not_rm                     = 0x02F7,
  x86_opcode_mul_eax_rm                 = 0x04F7,
  x86_opcode_imul_eax_rm                = 0x05F7,
  x86_opcode_idiv_eax_rm                = 0x07F7,
  x86_opcode_add_rm_imm                 = 0x0081,
  x86_opcode_and_rm_imm                 = 0x0481,
  x86_opcode_sub_rm_imm                 = 0x0581,
  x86_opcode_xor_rm_imm                 = 0x0681,
  x86_opcode_add_reg_rm                 = 0x03,
  x86_opcode_adc_reg_rm                 = 0x13,
  x86_opcode_and_reg_rm                 = 0x23,
  x86_opcode_or_reg_rm                  = 0x0B,
  x86_opcode_sub_reg_rm                 = 0x2B,
  x86_opcode_sbb_reg_rm                 = 0x1B,
  x86_opcode_xor_reg_rm                 = 0x33,
  x86_opcode_cmp_reg_rm                 = 0x39,
  x86_opcode_cmp_rm_imm                 = 0x0781,
  x86_opcode_lea_reg_rm                 = 0x8D,
  x86_opcode_j                          = 0x80,
  x86_opcode_cdq                        = 0x99,
  x86_opcode_jmp                        = 0xE9,
  x86_opcode_jmp_reg                    = 0x04FF,
  x86_opcode_ext                        = 0x0F
} x86_opcodes;

typedef enum
{
  x86_opcode_seto                       = 0x90,
  x86_opcode_setc                       = 0x92,
  x86_opcode_setnc                      = 0x93,
  x86_opcode_setz                       = 0x94,
  x86_opcode_setnz                      = 0x95,
  x86_opcode_sets                       = 0x98,
  x86_opcode_setns                      = 0x99,
} x86_ext_opcodes;

typedef enum
{
  x86_condition_code_o                  = 0x00,
  x86_condition_code_no                 = 0x01,
  x86_condition_code_c                  = 0x02,
  x86_condition_code_nc                 = 0x03,
  x86_condition_code_z                  = 0x04,
  x86_condition_code_nz                 = 0x05,
  x86_condition_code_na                 = 0x06,
  x86_condition_code_a                  = 0x07,
  x86_condition_code_s                  = 0x08,
  x86_condition_code_ns                 = 0x09,
  x86_condition_code_p                  = 0x0A,
  x86_condition_code_np                 = 0x0B,
  x86_condition_code_l                  = 0x0C,
  x86_condition_code_nl                 = 0x0D,
  x86_condition_code_ng                 = 0x0E,
  x86_condition_code_g                  = 0x0F
} x86_condition_codes;

#define x86_relative_offset(source, offset, next)                             \
  ((u32)((uintptr_t)offset - ((uintptr_t)source + next)))                     \

#define x86_emit_opcode_1b_reg(opcode, dest, source)                          \
{                                                                             \
  x86_emit_byte(x86_opcode_##opcode);                                         \
  x86_emit_reg_op(dest, source);                                              \
}                                                                             \

#define x86_emit_opcode_1b_mem(opcode, dest, base, offset)                    \
{                                                                             \
  x86_emit_byte(x86_opcode_##opcode);                                         \
  x86_emit_mem_op(dest, base, offset);                                        \
}                                                                             \

#define x86_emit_opcode_1b_mem_sib(opcode, dest, base, ridx, scale, offset)   \
{                                                                             \
  x86_emit_byte(x86_opcode_##opcode);                                         \
  x86_emit_mem_sib_op(dest, base,                                             \
                      ridx, scale, offset);                                   \
}                                                                             \

#define x86_emit_opcode_1b(opcode, reg)                                       \
  x86_emit_byte(x86_opcode_##opcode | reg)                                    \

#define x86_emit_opcode_1b_ext_reg(opcode, dest)                              \
  x86_emit_byte(x86_opcode_##opcode & 0xFF);                                  \
  x86_emit_reg_op(x86_opcode_##opcode >> 8, dest)                             \

#define x86_emit_opcode_1b_ext_mem(opcode, base, offset)                      \
  x86_emit_byte(x86_opcode_##opcode & 0xFF);                                  \
  x86_emit_mem_op(x86_opcode_##opcode >> 8, base, offset)                     \

// Single byte opcode instructions
#define x86_emit_cdq()                                                        \
  x86_emit_byte(x86_opcode_cdq)                                               \

#define x86_emit_ret()                                                        \
  x86_emit_byte(x86_opcode_ret)                                               \

#define x86_emit_mov_reg_mem(dest, base, offset)                              \
  x86_emit_opcode_1b_mem(mov_reg_rm, dest, base, offset)                      \

#define x86_emit_mov_reg_mem_idx(dest, base, scale, index, offset)            \
  x86_emit_opcode_1b_mem_sib(mov_reg_rm, dest, base, index, scale, offset)    \

#define x86_emit_mov_mem_idx_reg(dest, base, scale, index, offset)            \
  x86_emit_opcode_1b_mem_sib(mov_rm_reg, dest, base, index, scale, offset)    \

#define x86_emit_mov_mem_reg(source, base, offset)                            \
  x86_emit_opcode_1b_mem(mov_rm_reg, source, base, offset)                    \

#define x86_emit_setcc_mem(ccode, base, offset)                               \
  x86_emit_byte(x86_opcode_ext);                                              \
  x86_emit_opcode_1b_mem(set##ccode, x86_reg_eax, base, offset);              \

#define x86_emit_add_reg_mem(dst, base, offset)                               \
  x86_emit_opcode_1b_mem(add_reg_rm, dst, base, offset);                      \

#define x86_emit_or_reg_mem(dst, base, offset)                                \
  x86_emit_opcode_1b_mem(or_reg_rm, dst, base, offset);                       \

#define x86_emit_xor_reg_mem(dst, base, offset)                               \
  x86_emit_opcode_1b_mem(xor_reg_rm, dst, base, offset);                      \

#define x86_emit_cmp_reg_mem(rega, base, offset)                              \
  x86_emit_opcode_1b_mem(cmp_reg_rm, rega, base, offset);                     \

#define x86_emit_test_reg_mem(rega, base, offset)                             \
  x86_emit_opcode_1b_mem(test_reg_rm, rega, base, offset);                    \

#define x86_emit_mov_reg_reg(dest, source)                                    \
  if (dest != source) {                                                       \
    x86_emit_opcode_1b_reg(mov_reg_rm, dest, source)                          \
  }                                                                           \

#define x86_emit_mov_reg_imm(dest, imm)                                       \
  x86_emit_opcode_1b(mov_reg_imm, dest);                                      \
  x86_emit_dword(imm)                                                         \

#define x86_emit_mov_mem_imm(imm, base, offset)                               \
  x86_emit_opcode_1b_ext_mem(mov_rm_imm, base, offset);                       \
  x86_emit_dword(imm)                                                         \

#define x86_emit_and_mem_imm(imm, base, offset)                               \
  x86_emit_opcode_1b_ext_mem(and_rm_imm, base, offset);                       \
  x86_emit_dword(imm)                                                         \

#define x86_emit_shl_reg_imm(dest, imm)                                       \
  x86_emit_opcode_1b_ext_reg(shl_reg_imm, dest);                              \
  x86_emit_byte(imm)                                                          \

#define x86_emit_shr_reg_imm(dest, imm)                                       \
  x86_emit_opcode_1b_ext_reg(shr_reg_imm, dest);                              \
  x86_emit_byte(imm)                                                          \

#define x86_emit_sar_reg_imm(dest, imm)                                       \
  x86_emit_opcode_1b_ext_reg(sar_reg_imm, dest);                              \
  x86_emit_byte(imm)                                                          \

#define x86_emit_ror_reg_imm(dest, imm)                                       \
  x86_emit_opcode_1b_ext_reg(ror_reg_imm, dest);                              \
  x86_emit_byte(imm)                                                          \

#define x86_emit_add_reg_reg(dest, source)                                    \
  x86_emit_opcode_1b_reg(add_reg_rm, dest, source)                            \

#define x86_emit_adc_reg_reg(dest, source)                                    \
  x86_emit_opcode_1b_reg(adc_reg_rm, dest, source)                            \

#define x86_emit_sub_reg_reg(dest, source)                                    \
  x86_emit_opcode_1b_reg(sub_reg_rm, dest, source)                            \

#define x86_emit_sbb_reg_reg(dest, source)                                    \
  x86_emit_opcode_1b_reg(sbb_reg_rm, dest, source)                            \

#define x86_emit_and_reg_reg(dest, source)                                    \
  x86_emit_opcode_1b_reg(and_reg_rm, dest, source)                            \

#define x86_emit_or_reg_reg(dest, source)                                     \
  x86_emit_opcode_1b_reg(or_reg_rm, dest, source)                             \

#define x86_emit_xor_reg_reg(dest, source)                                    \
  x86_emit_opcode_1b_reg(xor_reg_rm, dest, source)                            \

#define x86_emit_add_reg_imm(dest, imm)                                       \
  if(imm != 0)                                                                \
  {                                                                           \
    x86_emit_opcode_1b_ext_reg(add_rm_imm, dest);                             \
    x86_emit_dword(imm);                                                      \
  }                                                                           \

#define x86_emit_sub_reg_imm(dest, imm)                                       \
  if(imm != 0)                                                                \
  {                                                                           \
    x86_emit_opcode_1b_ext_reg(sub_rm_imm, dest);                             \
    x86_emit_dword(imm);                                                      \
  }                                                                           \

#define x86_emit_and_reg_imm(dest, imm)                                       \
  x86_emit_opcode_1b_ext_reg(and_rm_imm, dest);                               \
  x86_emit_dword(imm)                                                         \

#define x86_emit_xor_reg_imm(dest, imm)                                       \
  x86_emit_opcode_1b_ext_reg(xor_rm_imm, dest);                               \
  x86_emit_dword(imm)                                                         \

#define x86_emit_test_reg_imm(dest, imm)                                      \
  x86_emit_opcode_1b_ext_reg(test_rm_imm, dest);                              \
  x86_emit_dword(imm)                                                         \

#define x86_emit_cmp_reg_reg(dest, source)                                    \
  x86_emit_opcode_1b_reg(cmp_reg_rm, dest, source)                            \

#define x86_emit_test_reg_reg(dest, source)                                   \
  x86_emit_opcode_1b_reg(test_reg_rm, dest, source)                           \

#define x86_emit_cmp_reg_imm(dest, imm)                                       \
  x86_emit_opcode_1b_ext_reg(cmp_rm_imm, dest);                               \
  x86_emit_dword(imm)                                                         \

#define x86_emit_rot_reg_reg(type, dest)                                      \
  x86_emit_opcode_1b_ext_reg(type##_reg_rm, dest)                             \

#define x86_emit_rot_reg1(type, dest)                                         \
  x86_emit_opcode_1b_ext_reg(type##_reg1, dest)                               \

#define x86_emit_shr_reg_reg(dest)                                            \
  x86_emit_opcode_1b_ext_reg(shr_reg_rm, dest)                                \

#define x86_emit_sar_reg_reg(dest)                                            \
  x86_emit_opcode_1b_ext_reg(sar_reg_rm, dest)                                \

#define x86_emit_shl_reg_reg(dest)                                            \
  x86_emit_opcode_1b_ext_reg(shl_reg_rm, dest)                                \

#define x86_emit_mul_eax_reg(source)                                          \
  x86_emit_opcode_1b_ext_reg(mul_eax_rm, source)                              \

#define x86_emit_imul_eax_reg(source)                                         \
  x86_emit_opcode_1b_ext_reg(imul_eax_rm, source)                             \

#define x86_emit_idiv_eax_reg(source)                                         \
  x86_emit_opcode_1b_ext_reg(idiv_eax_rm, source)                             \

#define x86_emit_not_reg(srcdst)                                              \
  x86_emit_opcode_1b_ext_reg(not_rm, srcdst)                                  \

#define x86_emit_call_offset(relative_offset)                                 \
  x86_emit_byte(x86_opcode_call_offset);                                      \
  x86_emit_dword(relative_offset)                                             \

#define x86_emit_lea_reg_mem(dest, base, offset)                              \
  x86_emit_opcode_1b_mem(lea_reg_rm, dest, base, offset)                      \

#define x86_emit_j_filler(condition_code, writeback_location)                 \
  x86_emit_byte(x86_opcode_ext);                                              \
  x86_emit_byte(x86_opcode_j | condition_code);                               \
  (writeback_location) = translation_ptr;                                     \
  translation_ptr += 4                                                        \

#define x86_emit_j_offset(condition_code, offset)                             \
  x86_emit_byte(x86_opcode_ext);                                              \
  x86_emit_byte(x86_opcode_j | condition_code);                               \
  x86_emit_dword(offset)                                                      \

#define x86_emit_jmp_filler(writeback_location)                               \
  x86_emit_byte(x86_opcode_jmp);                                              \
  (writeback_location) = translation_ptr;                                     \
  translation_ptr += 4                                                        \

#define x86_emit_jmp_offset(offset)                                           \
  x86_emit_byte(x86_opcode_jmp);                                              \
  x86_emit_dword(offset)                                                      \

#define x86_emit_jmp_reg(source)                                              \
  x86_emit_opcode_1b_ext_reg(jmp_reg, source)                                 \


/* Offsets from reg_base, see stub.S */
#define SPSR_BASE_OFF   0xA9100

#define generate_test_imm(ireg, imm)                                          \
  x86_emit_test_reg_imm(reg_##ireg, imm);                                     \

#define generate_test_memreg(ireg_ref, arm_reg_src)                           \
  x86_emit_test_reg_mem(reg_##ireg_ref, reg_base, arm_reg_src * 4)            \

#define generate_cmp_memreg(ireg_ref, arm_reg_src)                            \
  x86_emit_cmp_reg_mem(reg_##ireg_ref, reg_base, arm_reg_src * 4)             \

#define generate_cmp_imm(ireg, imm)                                           \
  x86_emit_cmp_reg_imm(reg_##ireg, imm)                                       \

#define generate_cmp_reg(ireg, ireg2)                                         \
  x86_emit_cmp_reg_reg(reg_##ireg, reg_##ireg2)                               \

#define generate_update_flag(condcode, regnum)                                \
  x86_emit_setcc_mem(condcode, reg_base, regnum * 4)                          \

#define generate_load_spsr(ireg, idxr)                                        \
  x86_emit_mov_reg_mem_idx(reg_##ireg, reg_base, 2, reg_##idxr, SPSR_BASE_OFF);

#define generate_store_spsr(ireg, idxr)                                       \
  x86_emit_mov_mem_idx_reg(reg_##ireg, reg_base, 2, reg_##idxr, SPSR_BASE_OFF);

#define generate_load_reg(ireg, reg_index)                                    \
  x86_emit_mov_reg_mem(reg_##ireg, reg_base, reg_index * 4);                  \

#define generate_load_pc(ireg, new_pc)                                        \
  x86_emit_mov_reg_imm(reg_##ireg, (new_pc))                                  \

#define generate_load_imm(ireg, imm)                                          \
  x86_emit_mov_reg_imm(reg_##ireg, imm)                                       \

#define generate_store_reg(ireg, reg_index)                                   \
  x86_emit_mov_mem_reg(reg_##ireg, reg_base, (reg_index) * 4)                 \

#define generate_store_reg_i32(imm32, reg_index)                              \
  x86_emit_mov_mem_imm((imm32), reg_base, (reg_index) * 4)                    \

#define generate_shift_left(ireg, imm)                                        \
  x86_emit_shl_reg_imm(reg_##ireg, imm)                                       \

#define generate_shift_left_var(ireg)                                         \
  x86_emit_shl_reg_reg(reg_##ireg)                                            \

#define generate_shift_right(ireg, imm)                                       \
  x86_emit_shr_reg_imm(reg_##ireg, imm)                                       \

#define generate_shift_right_var(ireg)                                        \
  x86_emit_shr_reg_reg(reg_##ireg)                                            \

#define generate_shift_right_arithmetic(ireg, imm)                            \
  x86_emit_sar_reg_imm(reg_##ireg, imm)                                       \

#define generate_shift_right_arithmetic_var(ireg)                             \
  x86_emit_sar_reg_reg(reg_##ireg)                                            \

#define generate_rotate_right(ireg, imm)                                      \
  x86_emit_ror_reg_imm(reg_##ireg, imm)                                       \

#define generate_rotate_right_var(ireg)                                       \
  x86_emit_rot_reg_reg(ror, reg_##ireg)                                       \

#define generate_rcr(ireg)                                                    \
  x86_emit_rot_reg_reg(rcr, reg_##ireg)                                       \

#define generate_rcr1(ireg)                                                   \
  x86_emit_rot_reg1(rcr, reg_##ireg)                                          \

#define generate_and_mem(imm, ireg_base, offset)                              \
  x86_emit_and_mem_imm(imm, reg_##ireg_base, (offset))                        \

#define generate_and(ireg_dest, ireg_src)                                     \
  x86_emit_and_reg_reg(reg_##ireg_dest, reg_##ireg_src)                       \

#define generate_add(ireg_dest, ireg_src)                                     \
  x86_emit_add_reg_reg(reg_##ireg_dest, reg_##ireg_src)                       \

#define generate_adc(ireg_dest, ireg_src)                                     \
  x86_emit_adc_reg_reg(reg_##ireg_dest, reg_##ireg_src)                       \

#define generate_add_memreg(ireg_dest, arm_reg_src)                           \
  x86_emit_add_reg_mem(reg_##ireg_dest, reg_base, arm_reg_src * 4)            \

#define generate_sub(ireg_dest, ireg_src)                                     \
  x86_emit_sub_reg_reg(reg_##ireg_dest, reg_##ireg_src)                       \

#define generate_sbb(ireg_dest, ireg_src)                                     \
  x86_emit_sbb_reg_reg(reg_##ireg_dest, reg_##ireg_src)                       \

#define generate_or(ireg_dest, ireg_src)                                      \
  x86_emit_or_reg_reg(reg_##ireg_dest, reg_##ireg_src)                        \

#define generate_or_mem(ireg_dest, arm_reg_src)                               \
  x86_emit_or_reg_mem(reg_##ireg_dest, reg_base, arm_reg_src * 4)             \

#define generate_xor(ireg_dest, ireg_src)                                     \
  x86_emit_xor_reg_reg(reg_##ireg_dest, reg_##ireg_src)                       \

#define generate_xor_mem(ireg_dest, arm_reg_src)                              \
  x86_emit_xor_reg_mem(reg_##ireg_dest, reg_base, arm_reg_src * 4)            \

#define generate_add_imm(ireg, imm)                                           \
  x86_emit_add_reg_imm(reg_##ireg, imm)                                       \

#define generate_sub_imm(ireg, imm)                                           \
  x86_emit_sub_reg_imm(reg_##ireg, imm)                                       \

#define generate_xor_imm(ireg, imm)                                           \
  x86_emit_xor_reg_imm(reg_##ireg, imm)                                       \

#define generate_add_reg_reg_imm(ireg_dest, ireg_src, imm)                    \
  x86_emit_lea_reg_mem(reg_##ireg_dest, reg_##ireg_src, imm)                  \

#define generate_and_imm(ireg, imm)                                           \
  x86_emit_and_reg_imm(reg_##ireg, imm)                                       \

#define generate_mov(ireg_dest, ireg_src)                                     \
  x86_emit_mov_reg_reg(reg_##ireg_dest, reg_##ireg_src)                       \

#define generate_not(ireg)                                                    \
  x86_emit_not_reg(reg_##ireg)                                                \

#define generate_multiply(ireg)                                               \
  x86_emit_imul_eax_reg(reg_##ireg)                                           \

#define generate_multiply_s64(ireg)                                           \
  x86_emit_imul_eax_reg(reg_##ireg)                                           \

#define generate_multiply_u64(ireg)                                           \
  x86_emit_mul_eax_reg(reg_##ireg)                                            \

#define generate_multiply_s64_add(ireg_src, ireg_lo, ireg_hi)                 \
  x86_emit_imul_eax_reg(reg_##ireg_src);                                      \
  x86_emit_add_reg_reg(reg_a0, reg_##ireg_lo);                                \
  x86_emit_adc_reg_reg(reg_a1, reg_##ireg_hi)                                 \

#define generate_multiply_u64_add(ireg_src, ireg_lo, ireg_hi)                 \
  x86_emit_mul_eax_reg(reg_##ireg_src);                                       \
  x86_emit_add_reg_reg(reg_a0, reg_##ireg_lo);                                \
  x86_emit_adc_reg_reg(reg_a1, reg_##ireg_hi)                                 \


#define generate_function_call(function_location)                             \
  x86_emit_call_offset(x86_relative_offset(translation_ptr,                   \
   function_location, 4));                                                    \

#define generate_exit_block()                                                 \
  x86_emit_ret();                                                             \

#define generate_cycle_update()                                               \
  x86_emit_sub_reg_imm(reg_cycles, cycle_count);                              \
  cycle_count = 0                                                             \

#define generate_branch_patch_conditional(dest, offset)                       \
  *((u32 *)(dest)) = x86_relative_offset(dest, offset, 4)                     \

#define generate_branch_patch_unconditional(dest, offset)                     \
  *((u32 *)(dest)) = x86_relative_offset(dest, offset, 4)                     \


#endif
