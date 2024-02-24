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

#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

void init_cpu();

// CPU mode macros and helpers
// Discards privilege bit
#define REG_MODE(m) (reg_mode[(m) & 0xF])
#define REG_SPSR(m) (spsr[(m) & 0xF])
#define PRIVMODE(m) ((m) >> 4)

#define CPU_ACTIVE          0
#define CPU_HALT            1
#define CPU_STOP            2
#define CPU_DMA             3  /* CPU is idling due to DMA transfer */

typedef enum {
  // CPU status & registers
  REG_SP            = 13,
  REG_LR            = 14,
  REG_PC            = 15,
  REG_CPSR          = 16,
  CPU_MODE          = 17,
  CPU_HALT_STATE    = 18,
  REG_ARCH_COUNT    = 19,

  // This is saved separately
  REG_BUS_VALUE     = 19,

  // Dynarec signaling and spilling
  // (Not really part of the CPU state)
  REG_N_FLAG        = 20,
  REG_Z_FLAG        = 21,
  REG_C_FLAG        = 22,
  REG_V_FLAG        = 23,
  REG_SLEEP_CYCLES  = 24,
  OAM_UPDATED       = 25,
  REG_SAVE          = 26,
  REG_SAVE2         = 27,
  REG_SAVE3         = 28,
  REG_SAVE4         = 29,
  REG_SAVE5         = 30,
  REG_SAVE6         = 31,

  /* Machine defined storage */
  REG_USERDEF       = 32,

  REG_MAX           = 64
} ext_reg_numbers;

typedef u32 cpu_mode_type;

// Bit 4 indicates privilege level
#define MODE_USER         0x00   // Non-privileged mode
#define MODE_SYSTEM       0x10   // Privileged modes
#define MODE_IRQ          0x11
#define MODE_FIQ          0x12
#define MODE_SUPERVISOR   0x13
#define MODE_ABORT        0x14
#define MODE_UNDEFINED    0x15
#define MODE_INVALID      0x16

// Lookup tables used for CPU mode changing
extern const u32 cpu_modes[16];
extern const u32 cpsr_masks[4][2];
extern const u32 spsr_masks[4];

// Changes the CPU mode (and banks registers in and out as needed).
void set_cpu_mode(cpu_mode_type new_mode);

// Memory handler (and instruction) side-effect reporting.
typedef u8 cpu_alert_type;

#define CPU_ALERT_NONE         0    // No side effects
#define CPU_ALERT_HALT   (1 << 0)   // The CPU is halted, stop executing.
#define CPU_ALERT_SMC    (1 << 1)   // JIT emitted code was overwritten.
#define CPU_ALERT_IRQ    (1 << 2)   // An IRQ was flagged.

// Interrupt related code
typedef u16 irq_type;

#define IRQ_NONE     0x0000
#define IRQ_VBLANK   0x0001
#define IRQ_HBLANK   0x0002
#define IRQ_VCOUNT   0x0004
#define IRQ_TIMER0   0x0008
#define IRQ_TIMER1   0x0010
#define IRQ_TIMER2   0x0020
#define IRQ_TIMER3   0x0040
#define IRQ_SERIAL   0x0080
#define IRQ_DMA0     0x0100
#define IRQ_DMA1     0x0200
#define IRQ_DMA2     0x0400
#define IRQ_DMA3     0x0800
#define IRQ_KEYPAD   0x1000
#define IRQ_GAMEPAK  0x2000

// Checks if an IRQ is pending and processes it (by changing the CPU mode and PC)
u32 check_and_raise_interrupts(void);
// Returns if there's a pending interrupt
cpu_alert_type check_interrupt(void);
// Flags an interrupt, but doesn't immediately raise it.
cpu_alert_type flag_interrupt(irq_type irq_raised);

// Savetstates
bool cpu_check_savestate(const u8 *src);
unsigned cpu_write_savestate(u8* dst);
bool cpu_read_savestate(const u8 *src);


// Memory structure definitions for the CPU.
extern u32 reg[64];
extern u32 reg_mode[7][7];
extern u32 spsr[6];


#ifdef __cplusplus
}
#endif

