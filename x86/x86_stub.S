# gameplaySP
#
# Copyright (C) 2006 Exophase <exophase@gmail.com>
#
# This program is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License as
# published by the Free Software Foundation; either version 2 of
# the License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
# General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA

#include "../gpsp_config.h"

.align 4

#define defsymbl(symbol) \
.global symbol ;         \
.global _##symbol ;      \
symbol:                  \
_##symbol:

#ifndef _WIN32
# External symbols (data + functions)
#define _iwram iwram
#define _ewram ewram
#define _vram vram
#define _oam_ram oam_ram
#define _bios_rom bios_rom
#define _io_registers io_registers

#define _update_gba update_gba
#define _block_lookup_address_arm block_lookup_address_arm
#define _block_lookup_address_thumb block_lookup_address_thumb
#define _block_lookup_address_dual block_lookup_address_dual
#define _write_io_register8 write_io_register8
#define _write_io_register16 write_io_register16
#define _write_io_register32 write_io_register32
#define _flush_translation_cache_ram flush_translation_cache_ram
#define _write_eeprom write_eeprom
#define _write_backup write_backup
#define _write_rtc write_rtc
#define _execute_store_cpsr_body execute_store_cpsr_body
#endif

.global _iwram
.global _ewram
.global _vram
.global _oam_ram
.global _bios_rom
.global _io_registers

.extern _spsr

.equ REG_SP,            (13 * 4)
.equ REG_LR,            (14 * 4)
.equ REG_PC,            (15 * 4)
.equ REG_N_FLAG,        (16 * 4)
.equ REG_Z_FLAG,        (17 * 4)
.equ REG_C_FLAG,        (18 * 4)
.equ REG_V_FLAG,        (19 * 4)
.equ REG_CPSR,          (20 * 4)
.equ REG_SAVE,          (21 * 4)
.equ REG_SAVE2,         (22 * 4)
.equ REG_SAVE3,         (23 * 4)
.equ CPU_MODE,          (29 * 4)
.equ CPU_HALT_STATE,    (30 * 4)
.equ CHANGED_PC_STATUS, (31 * 4)
.equ COMPLETED_FRAME,   (32 * 4)
.equ OAM_UPDATED,       (33 * 4)

# destroys ecx and edx

.macro collapse_flag offset, shift
  mov \offset(%ebx), %ecx
  shl $\shift, %ecx
  or %ecx, %edx
.endm

.macro collapse_flags_no_update
  xor %edx, %edx
  collapse_flag REG_N_FLAG, 31
  collapse_flag REG_Z_FLAG, 30
  collapse_flag REG_C_FLAG, 29
  collapse_flag REG_V_FLAG, 28
  mov REG_CPSR(%ebx), %ecx
  and $0xFF, %ecx
  or %ecx, %edx
.endm


.macro collapse_flags
  collapse_flags_no_update
  mov %edx, REG_CPSR(%ebx)
.endm

.macro extract_flag shift, offset
  mov REG_CPSR(%ebx), %edx
  shr $\shift, %edx
  and $0x01, %edx
  mov %edx, \offset(%ebx)
.endm

.macro extract_flags
  extract_flag 31, REG_N_FLAG
  extract_flag 30, REG_Z_FLAG
  extract_flag 29, REG_C_FLAG
  extract_flag 28, REG_V_FLAG
.endm

# Process a hardware event. Since an interrupt might be
# raised we have to check if the PC has changed.

# eax: current address

st:
  .asciz "u\n"

defsymbl(x86_update_gba)
  mov %eax, REG_PC(%ebx)      # current PC = eax
  collapse_flags              # update cpsr, trashes ecx and edx

  call _update_gba            # process the next event

  mov %eax, %edi              # edi = new cycle count

  # did we just complete a frame? go back to main then
  cmpl $0, COMPLETED_FRAME(%ebx)
  jne return_to_main

  # did the PC change?
  cmpl $1, CHANGED_PC_STATUS(%ebx)
  je lookup_pc
  ret                         # if not, go back to caller

# Perform this on an indirect branch that will definitely go to
# ARM code, IE anything that changes the PC in ARM mode except
# for BX and data processing to PC with the S bit set.

# eax: GBA address to branch to
# edi: Cycle counter

defsymbl(x86_indirect_branch_arm)
  call _block_lookup_address_arm
  jmp *%eax

# For indirect branches that'll definitely go to Thumb. In
# Thumb mode any indirect branches except for BX.

defsymbl(x86_indirect_branch_thumb)
  call _block_lookup_address_thumb
  jmp *%eax

# For indirect branches that can go to either Thumb or ARM,
# mainly BX (also data processing to PC with S bit set, be
# sure to adjust the target with a 1 in the lowest bit for this)

defsymbl(x86_indirect_branch_dual)
  call _block_lookup_address_dual
  jmp *%eax


# General ext memory routines

ext_store_ignore:
  ret                         # ignore these writes

write_epilogue:
  cmp $0, %eax                # 0 return means nothing happened
  jz no_alert                 # if so we can leave

  collapse_flags              # make sure flags are good for function call
  cmp $2, %eax                # see if it was an SMC trigger
  je smc_write

alert_loop:
  call _update_gba            # process the next event
  
  # did we just complete a frame? go back to main then
  cmpl $0, COMPLETED_FRAME(%ebx)
  jne return_to_main

  # see if the halt status has changed
  mov CPU_HALT_STATE(%ebx), %edx

  cmp $0, %edx                # 0 means it has
  jnz alert_loop              # if not go again

  mov %eax, %edi              # edi = new cycle count
  jmp lookup_pc               # pc has definitely changed

no_alert:
  ret

ext_store_eeprom:
  jmp _write_eeprom           # perform eeprom write


# 8bit ext memory routines

ext_store_iwram8:
  and $0x7FFF, %eax                 # wrap around address
  mov %dl, (_iwram+0x8000)(%eax)    # perform store
  cmpb $0, _iwram(%eax)             # Check SMC mirror
  jne smc_write
  ret

ext_store_ewram8:
  and $0x3FFFF, %eax                # wrap around address
  mov %dl, _ewram(%eax)             # perform store
  cmpb $0, (_ewram+0x40000)(%eax)   # Check SMC mirror
  jne smc_write
  ret

ext_store_io8:
  and $0x3FF, %eax            # wrap around address
  and $0xFF, %edx
  call _write_io_register8    # perform 8bit I/O register write
  jmp write_epilogue          # see if it requires any system update

ext_store_palette8:
  and $0x3FE, %eax            # wrap around address and align to 16bits
  jmp ext_store_palette16b    # perform 16bit palette write

ext_store_vram8:
  and $0x1FFFE, %eax          # wrap around address and align to 16bits
  mov %dl, %dh                # copy lower 8bits of value into full 16bits
  cmp $0x18000, %eax          # see if address is in upper region
  jb ext_store_vram8b
  sub $0x8000, %eax           # if so wrap down

ext_store_vram8b:
  mov %dx, _vram(%eax)        # perform 16bit store
  ret

ext_store_oam8:
  movl $1, OAM_UPDATED(%ebx)  # flag OAM update
  and $0x3FE, %eax            # wrap around address and align to 16bits
  mov %dl, %dh                # copy lower 8bits of value into full 16bits
  mov %dx, _oam_ram(%eax)     # perform 16bit store
  ret

ext_store_backup:
  and $0xFF, %edx             # make value 8bit
  and $0xFFFF, %eax           # mask address
  jmp _write_backup           # perform backup write

ext_store_u8_jtable:
  .long ext_store_ignore      # 0x00 BIOS, ignore
  .long ext_store_ignore      # 0x01 invalid, ignore
  .long ext_store_ewram8      # 0x02 EWRAM
  .long ext_store_iwram8      # 0x03 IWRAM
  .long ext_store_io8         # 0x04 I/O registers
  .long ext_store_palette8    # 0x05 Palette RAM
  .long ext_store_vram8       # 0x06 VRAM
  .long ext_store_oam8        # 0x07 OAM RAM
  .long ext_store_ignore      # 0x08 gamepak (no RTC accepted in 8bit)
  .long ext_store_ignore      # 0x09 gamepak, ignore
  .long ext_store_ignore      # 0x0A gamepak, ignore
  .long ext_store_ignore      # 0x0B gamepak, ignore
  .long ext_store_ignore      # 0x0C gamepak, ignore
  .long ext_store_eeprom      # 0x0D EEPROM (possibly)
  .long ext_store_backup      # 0x0E Flash ROM/SRAM

# eax: address to write to
# edx: value to write
# ecx: current pc

defsymbl(execute_store_u8)
  mov %ecx, REG_PC(%ebx)      # write out the PC
  mov %eax, %ecx              # ecx = address
  shr $24, %ecx               # ecx = address >> 24
  cmp $15, %ecx
  ja ext_store_ignore
  # ecx = ext_store_u8_jtable[address >> 24]
  mov ext_store_u8_jtable(, %ecx, 4), %ecx
  jmp *%ecx                   # jump to table index

# 16bit ext memory routines

ext_store_iwram16:
  and $0x7FFF, %eax                 # wrap around address
  mov %dx, (_iwram+0x8000)(%eax)    # perform store
  cmpw $0, _iwram(%eax)             # Check SMC mirror
  jne smc_write
  ret

ext_store_ewram16:
  and $0x3FFFF, %eax                # wrap around address
  mov %dx, _ewram(%eax)             # perform store
  cmpw $0, (_ewram+0x40000)(%eax)   # Check SMC mirror
  jne smc_write
  ret

ext_store_io16:
  and $0x3FF, %eax            # wrap around address
  and $0xFFFF, %edx
  call _write_io_register16   # perform 16bit I/O register write
  jmp write_epilogue          # see if it requires any system update

ext_store_palette16:
  and $0x3FF, %eax            # wrap around address

ext_store_palette16b:         # entry point for 8bit write
  mov %dx, _palette_ram(%eax) # write out palette value
  mov %edx, %ecx              # cx = dx
  shl $11, %ecx               # cx <<= 11 (red component is in high bits)
  mov %dh, %cl                # bottom bits of cx = top bits of dx
  shr $2, %cl                 # move the blue component to the bottom of cl
  and $0x03E0, %dx            # isolate green component of dx
  shl $1, %dx                 # make green component 6bits
  or %edx, %ecx               # combine green component into ecx
  # write out the freshly converted palette value
  mov %cx, _palette_ram_converted(%eax)
  ret                         # done

ext_store_vram16:
  and $0x1FFFF, %eax          # wrap around address
  cmp $0x18000, %eax          # see if address is in upper region
  jb ext_store_vram16b
  sub $0x8000, %eax           # if so wrap down

ext_store_vram16b:
  mov %dx, _vram(%eax)        # perform 16bit store
  ret

ext_store_oam16:
  movl $1, OAM_UPDATED(%ebx)  # flag OAM update
  and $0x3FF, %eax            # wrap around address
  mov %dx, _oam_ram(%eax)     # perform 16bit store
  ret

ext_store_rtc:
  and $0xFFFF, %edx           # make value 16bit
  and $0xFF, %eax             # mask address
  jmp _write_rtc              # write out RTC register

ext_store_u16_jtable:
  .long ext_store_ignore      # 0x00 BIOS, ignore
  .long ext_store_ignore      # 0x01 invalid, ignore
  .long ext_store_ewram16     # 0x02 EWRAM
  .long ext_store_iwram16     # 0x03 IWRAM
  .long ext_store_io16        # 0x04 I/O registers
  .long ext_store_palette16   # 0x05 Palette RAM
  .long ext_store_vram16      # 0x06 VRAM
  .long ext_store_oam16       # 0x07 OAM RAM
  .long ext_store_rtc         # 0x08 gamepak or RTC
  .long ext_store_ignore      # 0x09 gamepak, ignore
  .long ext_store_ignore      # 0x0A gamepak, ignore
  .long ext_store_ignore      # 0x0B gamepak, ignore
  .long ext_store_ignore      # 0x0C gamepak, ignore
  .long ext_store_eeprom      # 0x0D EEPROM (possibly)
  .long ext_store_ignore      # 0x0E Flash ROM/SRAM must be 8bit

defsymbl(execute_store_u16)
  mov %ecx, REG_PC(%ebx)      # write out the PC
  and $~0x01, %eax            # fix alignment
  mov %eax, %ecx              # ecx = address
  shr $24, %ecx               # ecx = address >> 24
  cmp $15, %ecx
  ja ext_store_ignore
  # ecx = ext_store_u16_jtable[address >> 24]
  mov ext_store_u16_jtable(, %ecx, 4), %ecx
  jmp *%ecx                   # jump to table index

# 32bit ext memory routines

ext_store_iwram32:
  and $0x7FFF, %eax                 # wrap around address
  mov %edx, (_iwram+0x8000)(%eax)   # perform store
  cmpl $0, _iwram(%eax)             # Check SMC mirror

  jne smc_write
  ret

ext_store_ewram32:
  and $0x3FFFF, %eax                # wrap around address
  mov %edx, _ewram(%eax)            # perform store
  cmpl $0, (_ewram+0x40000)(%eax)   # Check SMC mirror
  jne smc_write
  ret

ext_store_io32:
  and $0x3FF, %eax            # wrap around address
  call _write_io_register32   # perform 32bit I/O register write
  jmp write_epilogue          # see if it requires any system update

ext_store_palette32:
  and $0x3FF, %eax            # wrap around address
  call ext_store_palette16b   # write first 16bits
  add $2, %eax                # go to next address
  shr $16, %edx               # go to next 16bits
  jmp ext_store_palette16b    # write next 16bits

ext_store_vram32:
  and $0x1FFFF, %eax          # wrap around address
  cmp $0x18000, %eax          # see if address is in upper region
  jb ext_store_vram32b
  sub $0x8000, %eax           # if so wrap down

ext_store_vram32b:
  mov %edx, _vram(%eax)       # perform 32bit store
  ret

ext_store_oam32:
  movl $1, OAM_UPDATED(%ebx)  # flag OAM update
  and $0x3FF, %eax            # wrap around address
  mov %edx, _oam_ram(%eax)    # perform 32bit store
  ret

ext_store_u32_jtable:
  .long ext_store_ignore      # 0x00 BIOS, ignore
  .long ext_store_ignore      # 0x01 invalid, ignore
  .long ext_store_ewram32     # 0x02 EWRAM
  .long ext_store_iwram32     # 0x03 IWRAM
  .long ext_store_io32        # 0x04 I/O registers
  .long ext_store_palette32   # 0x05 Palette RAM
  .long ext_store_vram32      # 0x06 VRAM
  .long ext_store_oam32       # 0x07 OAM RAM
  .long ext_store_ignore      # 0x08 gamepak, ignore (no RTC in 32bit)
  .long ext_store_ignore      # 0x09 gamepak, ignore
  .long ext_store_ignore      # 0x0A gamepak, ignore
  .long ext_store_ignore      # 0x0B gamepak, ignore
  .long ext_store_ignore      # 0x0C gamepak, ignore
  .long ext_store_eeprom      # 0x0D EEPROM (possibly)
  .long ext_store_ignore      # 0x0E Flash ROM/SRAM must be 8bit


defsymbl(execute_store_u32)
  mov %ecx, REG_PC(%ebx)      # write out the PC
  and $~0x03, %eax            # fix alignment
  mov %eax, %ecx              # ecx = address
  shr $24, %ecx               # ecx = address >> 24
  cmp $15, %ecx
  ja ext_store_ignore
  # ecx = ext_store_u32_jtable[address >> 24]
  mov ext_store_u32_jtable(, %ecx, 4), %ecx
  jmp *%ecx

# %eax = new_cpsr
# %edx = store_mask

defsymbl(execute_store_cpsr)
  mov %edx, REG_SAVE(%ebx)        # save store_mask
  mov %ecx, REG_SAVE2(%ebx)       # save PC too

  mov %eax, %ecx                  # ecx = new_cpsr
  and %edx, %ecx                  # ecx = new_cpsr & store_mask
  mov REG_CPSR(%ebx), %eax        # eax = cpsr
  not %edx                        # edx = ~store_mask
  and %edx, %eax                  # eax = cpsr & ~store_mask
  or %ecx, %eax                   # eax = new cpsr combined with old

  call _execute_store_cpsr_body   # do the dirty work in this C function

  extract_flags                   # pull out flag vars from new CPSR

  cmp $0, %eax                    # see if return value is 0
  jnz changed_pc_cpsr             # might have changed the PC

  ret                             # return

changed_pc_cpsr:
  add $4, %esp                    # get rid of current return address
  call _block_lookup_address_arm  # lookup new PC
  jmp *%eax

smc_write:
  call _flush_translation_cache_ram

lookup_pc:
  add $4, %esp                       # Can't return, discard addr
  movl $0, CHANGED_PC_STATUS(%ebx)   # Lookup new block and jump to it
  mov REG_PC(%ebx), %eax
  testl $0x20, REG_CPSR(%ebx)
  jz lookup_pc_arm

lookup_pc_thumb:
  call _block_lookup_address_thumb
  jmp *%eax

lookup_pc_arm:
  call _block_lookup_address_arm
  jmp *%eax

# eax: cycle counter

defsymbl(execute_arm_translate)
  # Save main context, since we need to return gracefully
  pushl %ebx
  pushl %esi
  pushl %edi
  pushl %ebp

  movl $_reg, %ebx            # load base register
  extract_flags               # load flag variables
  movl %eax, %edi             # load edi cycle counter

  movl REG_PC(%ebx), %eax     # load PC

  # (if the CPU is halted, do not start executing but
  #  loop in the alert loop until it wakes up)
  cmpl $0, CPU_HALT_STATE(%ebx)
  je 1f
  call alert_loop     # Need to push something to the stack
  
1:
  testl $0x20, REG_CPSR(%ebx)
  jnz 2f

  call _block_lookup_address_arm
  jmp *%eax                   # jump to it

2:
  call _block_lookup_address_thumb
  jmp *%eax

return_to_main:
  add $4, %esp             # remove current return addr
  popl %ebp
  popl %edi
  popl %esi
  popl %ebx
  ret

.data
.align 64

defsymbl(reg)
  .space 0x100, 0
defsymbl(palette_ram)
  .space 0x400
defsymbl(palette_ram_converted)
  .space 0x400
defsymbl(oam_ram)
  .space 0x400
defsymbl(spsr)
  .space 24
defsymbl(reg_mode)
  .space 196

defsymbl(memory_map_read)
  .space 0x8000

#if !defined(HAVE_MMAP)

# Make this section executable!
.text
.section .jit,"awx",%nobits
.align 4
defsymbl(rom_translation_cache)
  .space ROM_TRANSLATION_CACHE_SIZE
defsymbl(ram_translation_cache)
  .space RAM_TRANSLATION_CACHE_SIZE

#endif

