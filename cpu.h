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

#ifndef CPU_H
#define CPU_H

#ifdef __cplusplus
extern "C" {
#endif

#include <stdbool.h>
#include "gpsp_config.h"

extern u32 instruction_count;

void execute_arm(u32 cycles);

u32 function_cc execute_load_u8(u32 address);
u32 function_cc execute_load_u16(u32 address);
u32 function_cc execute_load_u32(u32 address);
u32 function_cc execute_load_s8(u32 address);
u32 function_cc execute_load_s16(u32 address);
void function_cc execute_store_u8(u32 address, u32 source);
void function_cc execute_store_u16(u32 address, u32 source);
void function_cc execute_store_u32(u32 address, u32 source);
void function_cc execute_store_aligned_u32(u32 address, u32 source);
u32 execute_arm_translate(u32 cycles);
void init_translater(void);

u8 function_cc *block_lookup_address_arm(u32 pc);
u8 function_cc *block_lookup_address_thumb(u32 pc);
u8 function_cc *block_lookup_address_dual(u32 pc);
bool translate_block_arm(u32 pc, bool ram_region);
bool translate_block_thumb(u32 pc, bool ram_region);

#if defined(MMAP_JIT_CACHE)
extern u8* rom_translation_cache;
extern u8* ram_translation_cache;
#elif defined(_3DS)
#define rom_translation_cache ((u8*)0x02000000 - ROM_TRANSLATION_CACHE_SIZE)
#define ram_translation_cache (rom_translation_cache - RAM_TRANSLATION_CACHE_SIZE)
extern u8* rom_translation_cache_ptr;
extern u8* ram_translation_cache_ptr;
#elif defined(VITA)
extern u8* rom_translation_cache;
extern u8* ram_translation_cache;
extern int sceBlock;
#else
extern u8 rom_translation_cache[ROM_TRANSLATION_CACHE_SIZE];
extern u8 ram_translation_cache[RAM_TRANSLATION_CACHE_SIZE];
#endif
extern u8 *rom_translation_ptr;
extern u8 *ram_translation_ptr;

#define MAX_TRANSLATION_GATES 8

extern u32 idle_loop_target_pc;
extern u32 translation_gate_targets;
extern u32 translation_gate_target_pc[MAX_TRANSLATION_GATES];

extern u32 rom_branch_hash[ROM_BRANCH_HASH_SIZE];

void flush_translation_cache_rom(void);
void flush_translation_cache_ram(void);
void dump_translation_cache(void);
void init_dynarec_caches(void);
void flush_dynarec_caches(void);
void init_emitter(bool);
void init_bios_hooks(void);

#ifdef __cplusplus
}
#endif

#endif
