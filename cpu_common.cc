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

#include "common.h"

// Common structures for the CPU state. These are usually defined by the dynarec
// for builds that support dynarec (for alignment and easy access).

#if !defined(HAVE_DYNAREC)
  u32 reg[64];
  u32 spsr[6];
  u32 reg_mode[7][7];
#endif

// Index by PRS fields (1 and 4 only!) and User-Privileged mode
// In user mode some bits are read only
// Bit #4 is always set to one (so all modes are 1XXXX)
// Reserved bits are always zero and cannot be modified
const u32 cpsr_masks[4][2] =
{
  // User, Privileged
  {0x00000000, 0x00000000},
  {0x00000020, 0x000000EF},
  {0xF0000000, 0xF0000000},
  {0xF0000020, 0xF00000EF}
};

// SPSR is always a privileged instruction
const u32 spsr_masks[4] = { 0x00000000, 0x000000EF, 0xF0000000, 0xF00000EF };

// Mode bits (CPSR) to mode map
const u32 cpu_modes[16] =
{
  MODE_USER, MODE_FIQ, MODE_IRQ, MODE_SUPERVISOR,
  MODE_INVALID, MODE_INVALID, MODE_INVALID, MODE_ABORT,
  MODE_INVALID, MODE_INVALID, MODE_INVALID, MODE_UNDEFINED, 
  MODE_INVALID, MODE_INVALID, MODE_INVALID, MODE_SYSTEM
};

// CPU initialization. Setup registers (GPR and extended) as well as
// basic CPU state and mode. Allows for BIOS and in-game booting.
void init_cpu() {
  // Initialize CPU registers
  memset(reg, 0, REG_USERDEF * sizeof(u32));
  memset(reg_mode, 0, sizeof(reg_mode));
  for (u32 i = 0; i < sizeof(spsr)/sizeof(spsr[0]); i++)
    spsr[i] = 0x00000010;

  reg[CPU_HALT_STATE] = CPU_ACTIVE;
  reg[REG_SLEEP_CYCLES] = 0;

  if (selected_boot_mode == boot_game) {
    reg[REG_SP] = 0x03007F00;
    reg[REG_PC] = 0x08000000;
    reg[REG_CPSR] = 0x0000001F;   // system mode
    reg[CPU_MODE] = MODE_SYSTEM;
  } else {
    reg[REG_SP] = 0x03007F00;
    reg[REG_PC] = 0x00000000;
    reg[REG_CPSR] = 0x00000013 | 0xC0;  // supervisor
    reg[CPU_MODE] = MODE_SUPERVISOR;
  }

  // Stack pointers are set by BIOS, we set them
  // nevertheless, should we not boot from BIOS
  REG_MODE(MODE_USER)[5] = 0x03007F00;
  REG_MODE(MODE_IRQ)[5] = 0x03007FA0;
  REG_MODE(MODE_FIQ)[5] = 0x03007FA0;
  REG_MODE(MODE_SUPERVISOR)[5] = 0x03007FE0;
}


// When a mode change occurs from non-FIQ to non-FIQ retire the current
// reg[13] and reg[14] into reg_mode[cpu_mode][5] and reg_mode[cpu_mode][6]
// respectively and load into reg[13] and reg[14] reg_mode[new_mode][5] and
// reg_mode[new_mode][6]. When swapping to/from FIQ retire/load reg[8]
// through reg[14] to/from reg_mode[MODE_FIQ][0] through reg_mode[MODE_FIQ][6].

void set_cpu_mode(cpu_mode_type new_mode) {
  cpu_mode_type cpu_mode = reg[CPU_MODE];

  if (cpu_mode == new_mode)
     return;

  if (new_mode == MODE_FIQ) {
     for (u32 i = 8; i < 15; i++)
        REG_MODE(cpu_mode)[i - 8] = reg[i];
  } else {
     REG_MODE(cpu_mode)[5] = reg[REG_SP];
     REG_MODE(cpu_mode)[6] = reg[REG_LR];
  }

  if(cpu_mode == MODE_FIQ) {
     for (u32 i = 8; i < 15; i++)
        reg[i] = REG_MODE(new_mode)[i - 8];
  } else {
     reg[REG_SP] = REG_MODE(new_mode)[5];
     reg[REG_LR] = REG_MODE(new_mode)[6];
  }

  reg[CPU_MODE] = new_mode;
}

inline bool cpu_has_interrupt() {
  return (!(reg[REG_CPSR] & 0x80) &&                     // Interrupts enabled in CPSR
          read_ioreg(REG_IME) &&                         // Global IME is also enabled
          (read_ioreg(REG_IE) & read_ioreg(REG_IF)));    // Any flagged and enabled?
}

// Returns whether the CPU has a pending interrupt.
cpu_alert_type check_interrupt() {
  return cpu_has_interrupt() ? CPU_ALERT_IRQ : CPU_ALERT_NONE;
}

// Checks for pending IRQs and raises them. This changes the CPU mode
// which means that it must be called with a valid CPU state.
u32 check_and_raise_interrupts()
{
  // Check any IRQ flag pending, IME and CPSR-IRQ enabled
  if (cpu_has_interrupt())
  {
    // Value after the FIQ returns, should be improved
    reg[REG_BUS_VALUE] = 0xe55ec002;

    // Interrupt handler in BIOS
    REG_MODE(MODE_IRQ)[6] = reg[REG_PC] + 4;
    REG_SPSR(MODE_IRQ) = reg[REG_CPSR];
    reg[REG_CPSR] = 0xD2;
    reg[REG_PC] = 0x00000018;

    set_cpu_mode(MODE_IRQ);

    // Wake up CPU if it is stopped/sleeping.
    if (reg[CPU_HALT_STATE] == CPU_STOP ||
        reg[CPU_HALT_STATE] == CPU_HALT)
      reg[CPU_HALT_STATE] = CPU_ACTIVE;

    return 1;
  }
  return 0;
}

// This function marks a pending interrupt but does not raise it.
// It simply updates IF register and returns whether the IRQ needs
// to be raised (that is, IE/IME/CPSR enable the IRQ).
// Safe to call via dynarec without proper registers saved.
cpu_alert_type flag_interrupt(irq_type irq_raised)
{
  // Flag interrupt
  write_ioreg(REG_IF, read_ioreg(REG_IF) | irq_raised);

  return check_interrupt();
}

// Memory timing tables

/* Memory timings */
const u8 ws012_nonseq[] = {4, 3, 2, 8};
const u8 ws0_seq[] = {2, 1};
const u8 ws1_seq[] = {4, 1};
const u8 ws2_seq[] = {8, 1};

/* Divided by region and bus width (16/32) */
u8 ws_cyc_seq[16][2] =
{
  { 1, 1 }, // BIOS
  { 1, 1 }, // Invalid
  { 3, 6 }, // EWRAM (default settings)
  { 1, 1 }, // IWRAM
  { 1, 1 }, // IO Registers
  { 1, 2 }, // Palette RAM
  { 1, 2 }, // VRAM
  { 1, 2 }, // OAM
  { 0, 0 }, // Gamepak (wait 0)
  { 0, 0 }, // Gamepak (wait 0)
  { 0, 0 }, // Gamepak (wait 1)
  { 0, 0 }, // Gamepak (wait 1)
  { 0, 0 }, // Gamepak (wait 2)
  { 0, 0 }, // Gamepak (wait 2)
  { 1, 1 }, // Invalid
  { 1, 1 }, // Invalid
};
u8 ws_cyc_nseq[16][2] =
{
  { 1, 1 }, // BIOS
  { 1, 1 }, // Invalid
  { 3, 6 }, // EWRAM (default settings)
  { 1, 1 }, // IWRAM
  { 1, 1 }, // IO Registers
  { 1, 2 }, // Palette RAM
  { 1, 2 }, // VRAM
  { 1, 2 }, // OAM
  { 0, 0 }, // Gamepak (wait 0)
  { 0, 0 }, // Gamepak (wait 0)
  { 0, 0 }, // Gamepak (wait 1)
  { 0, 0 }, // Gamepak (wait 1)
  { 0, 0 }, // Gamepak (wait 2)
  { 0, 0 }, // Gamepak (wait 2)
  { 1, 1 }, // Invalid
  { 1, 1 }, // Invalid
};

const u32 def_seq_cycles[16][2] =
{
  { 1, 1 }, // BIOS
  { 1, 1 }, // Invalid
  { 3, 6 }, // EWRAM (default settings)
  { 1, 1 }, // IWRAM
  { 1, 1 }, // IO Registers
  { 1, 2 }, // Palette RAM
  { 1, 2 }, // VRAM
  { 1, 2 }, // OAM
  { 3, 6 }, // Gamepak (wait 0)
  { 3, 6 }, // Gamepak (wait 0)
  { 5, 9 }, // Gamepak (wait 1)
  { 5, 9 }, // Gamepak (wait 1)
  { 9, 17 }, // Gamepak (wait 2)
  { 9, 17 }, // Gamepak (wait 2)
};

void reload_timing_info() {
  uint16_t waitcnt = read_ioreg(REG_WAITCNT);

  /* Sequential 16 and 32 bit accesses to ROM */
  ws_cyc_seq[0x8][0] = ws_cyc_seq[0x9][0] = 1 + ws0_seq[(waitcnt >>  4) & 1];
  ws_cyc_seq[0xA][0] = ws_cyc_seq[0xB][0] = 1 + ws1_seq[(waitcnt >>  7) & 1];
  ws_cyc_seq[0xC][0] = ws_cyc_seq[0xD][0] = 1 + ws2_seq[(waitcnt >> 10) & 1];

  /* 32 bit accesses just cost double due to 16 bit bus */
  for (int i = 0x8; i <= 0xD; i++)
    ws_cyc_seq[i][1] = ws_cyc_seq[i][0] * 2;

  /* Sequential 16 and 32 bit accesses to ROM */
  ws_cyc_nseq[0x8][0] = ws_cyc_nseq[0x9][0] = 1 + ws012_nonseq[(waitcnt >> 2) & 3];
  ws_cyc_nseq[0xA][0] = ws_cyc_nseq[0xB][0] = 1 + ws012_nonseq[(waitcnt >> 5) & 3];
  ws_cyc_nseq[0xC][0] = ws_cyc_nseq[0xD][0] = 1 + ws012_nonseq[(waitcnt >> 8) & 3];

  /* 32 bit accesses are a non-seq (16) + seq access (16) */
  for (int i = 0x8; i <= 0xD; i++)
    ws_cyc_nseq[i][1] = 1 + ws_cyc_nseq[i][0] + ws_cyc_seq[i][0];
}

// Savestate related routines (common to both dynarec and interpreter)


bool cpu_check_savestate(const u8 *src) {
  const u8 *cpudoc = bson_find_key(src, "cpu");
  if (!cpudoc)
    return false;

  return bson_contains_key(cpudoc, "bus-value", BSON_TYPE_INT32) &&
         bson_contains_key(cpudoc, "regs", BSON_TYPE_ARR) &&
         bson_contains_key(cpudoc, "spsr", BSON_TYPE_ARR) &&
         bson_contains_key(cpudoc, "regmod", BSON_TYPE_ARR);
}


bool cpu_read_savestate(const u8 *src) {
  const u8 *cpudoc = bson_find_key(src, "cpu");
  return bson_read_int32(cpudoc, "bus-value", &reg[REG_BUS_VALUE]) &&
         bson_read_int32_array(cpudoc, "regs", reg, REG_ARCH_COUNT) &&
         bson_read_int32_array(cpudoc, "spsr", spsr, 6) &&
         bson_read_int32_array(cpudoc, "regmod", (u32*)reg_mode, 7*7);
}

unsigned cpu_write_savestate(u8 *dst) {
  u8 *wbptr, *startp = dst;
  bson_start_document(dst, "cpu", wbptr);
  bson_write_int32array(dst, "regs", reg, REG_ARCH_COUNT);
  bson_write_int32array(dst, "spsr", spsr, 6);
  bson_write_int32array(dst, "regmod", reg_mode, 7*7);
  bson_write_int32(dst, "bus-value", reg[REG_BUS_VALUE]);

  bson_finish_document(dst, wbptr);
  return (unsigned int)(dst - startp);
}


