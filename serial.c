/* gameplaySP
 *
 * Copyright (C) 2023 David Guillen Fandos <david@davidgf.net>
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

t_emulated_serial_mode emu_serial_mode = SERIAL_EMUMODE_AUTO;

//static u32 serial_irq_cycles = 0;
u32 serial_irq_cycles = 0;

// Timings are very aproximate, hopefully they are good enough.
#define CLOCK_CYC_256KHZ_8BIT        524    // CLOCK / 256KHz * 8
#define CLOCK_CYC_256KHZ_32BIT      2097    // CLOCK / 256KHz * 32
#define CLOCK_CYC_2MHZ_8BIT           67    // CLOCK / 2MHz * 8
#define CLOCK_CYC_2MHZ_32BIT         268    // CLOCK / 2MHz * 32
#define CLOCK_CYC_64KHZ_32BIT       8192    // CLOCK / 64kHz * 32

// Timings for UART/Multiplayer mode. We assume aprox. 20 bauds per transfer
// (start, 16b data, stop, and some delay for SO->SI enable) per device.
// This means around ~700us per transfer at 115200bauds (compatible with Poke's
// 750us timeout, just slightly above).
#define CLOCK_CYC_115200B_4P      11651     // CLOCK / 115200 * 20bits * 4GBAs
#define CLOCK_CYC_57600B_4P       23302     // CLOCK / 57600 * 20bits * 4GBAs
#define CLOCK_CYC_38400B_4P       34953     // CLOCK / 38400 * 20bits * 4GBAs
#define CLOCK_CYC_9600B_4P       139810     // CLOCK / 9600 * 20bits * 4GBAs

static const u32 uart_cycles[] = {
  CLOCK_CYC_9600B_4P,
  CLOCK_CYC_38400B_4P,
  CLOCK_CYC_57600B_4P,
  CLOCK_CYC_115200B_4P,
};

//#define CLOCK_CYC_MAX_TIMEOUT   1677721  / 2    // ~100ms max latency
#define CLOCK_CYC_MAX_TIMEOUT      139810   // 1/2 frame

// Available serial modes
typedef enum {
  SERIAL_MODE_NORMAL      = 0,
  SERIAL_MODE_MULTI       = 1,
  SERIAL_MODE_UART        = 2,
  SERIAL_MODE_GPIO        = 3,
  SERIAL_MODE_JOYBUS      = 4,
} t_sermode;

// Bits that the user can actually write (the other ones are read-only)
static const u16 siocnt_mask[5] = {
  0x7FFB,    // SI is read-only.
  0x7F83,    // SI/SD, MP Id and Err are all read-only.
  0x7F8F,    // Empty/Full/Error bits are read-only.
  0x7000,    // Not accurate really, uses RCNT.
  0x7000,    // Not accurate really, uses other regs.
};

static void set_serial_mode(t_sermode mode) {
  switch (mode) {
  case SERIAL_MODE_NORMAL:
    // Clear the SI bit by default.
    write_ioreg(REG_SIOCNT, read_ioreg(REG_SIOCNT) & ~0x04);
    break;
  case SERIAL_MODE_MULTI:
    // Set the multiplayer bits correctly.
    {
      u16 r = read_ioreg(REG_SIOCNT) & ~0x007C;
      printf("Mode change bef %x\n", r);
      if (netpl_client_id)
        r |= 0x4;   // Child bit
      r |= (netpl_client_id & 0x3) << 4;  // Player ID
      r |= 0x8;    // All GBAs ready
      printf("Mode change up %x\n", r);
      write_ioreg(REG_SIOCNT, r);
    }
    break;
  default:
    break;
  };
}

static t_sermode get_serial_mode(u16 siocnt, u16 rcnt) {
  if (rcnt & 0x8000) {
    if (rcnt & 0x4000)
      return SERIAL_MODE_JOYBUS;
    else
      return SERIAL_MODE_GPIO;
  } else {
    if (siocnt & 0x2000)
      return (siocnt & 0x1000) ? SERIAL_MODE_UART : SERIAL_MODE_MULTI;
    else
      return SERIAL_MODE_NORMAL;
  }
}

cpu_alert_type write_rcnt(u16 value) {
  u16 pval = read_ioreg(REG_RCNT);
  u16 siocnt = read_ioreg(REG_SIOCNT);
  t_sermode oldmode = get_serial_mode(siocnt, pval);
  t_sermode newmode = get_serial_mode(siocnt, value);

  write_ioreg(REG_RCNT, value);

  if (oldmode != newmode)
    set_serial_mode(newmode);

  printf("RCNT %x\n", value);

  switch (newmode) {
  case SERIAL_MODE_GPIO:
    // Check if we are pulling PD high. This resets the RFU module.
    if (emu_serial_mode == SERIAL_EMUMODE_RFU) {
      if ((value & 0x20) && !(pval & 0x02))
        rfu_reset();
    }
    break;

  default:
    break;
  };

  return CPU_ALERT_NONE;
}

cpu_alert_type write_siocnt(u16 value) {
  u16 rcnt = read_ioreg(REG_RCNT);
  u16 oldval = read_ioreg(REG_SIOCNT);
  t_sermode oldmode = get_serial_mode(oldval, rcnt);
  t_sermode newmode = get_serial_mode(value, rcnt);
  u16 reg_mask = siocnt_mask[newmode];
  // Do not let user write all bits (some are protected)
  u16 newval = (value & reg_mask) | (oldval & ~reg_mask);
  printf("SIOCNT %x (old %x) [%llu]\n", newval, oldval, (u64)time(NULL));

  switch (newmode) {
  case SERIAL_MODE_NORMAL:
    // For connected Wireless devices
    if (emu_serial_mode == SERIAL_EMUMODE_RFU) {
      // If Start bit is set, we are in master mode (internal clock), and
      // there's no ongoing transmission, we start a transmission.
      if ((newval & 0x0080) && (newval & 0x1) && !serial_irq_cycles) {
        // We simulate the data is immediately sent to the RFU module
        // and some data is received back (we simulate some delay too).
        u32 rval = rfu_transfer(read_ioreg32(REG_SIODATA32_L));
        write_ioreg(REG_SIODATA32_L, rval & 0xFFFF);
        write_ioreg(REG_SIODATA32_H, rval >> 16);

        // We schedule a future event to clear the "working" bit
        // and potentially generate an IRQ.
        serial_irq_cycles = (newval & 0x2) ? CLOCK_CYC_2MHZ_8BIT :
                                             CLOCK_CYC_256KHZ_8BIT;
        if (newval & 0x1000)
          serial_irq_cycles <<= 2;   // 4 times longer to send 32 bits.

        // Already raise the SI bit (as busy)
        newval |= 0x04;
      }

      // RFU SI/SO ack logic emulation.
      if (newval & 0x1) {   // Clock internal (master mode)
        // When GBA goes busy (device should be already busy) we can switch to ready.
        if ((newval & 0x0008) && !(oldval & 0x0008))
          newval &= ~0x0004;
      } else {   // Clock external (slave mode)
        // If SO goes high we make SI go high as well, to signal busy.
        if ((newval & 0x0008) && !(oldval & 0x0008))
          newval |= 0x0004;
        // Once SO goes low (GBA not busy anymore), lower SI as well.
        if (!(newval & 0x0008) && (oldval & 0x0008))
          newval &= ~0x0004;
      }
    }
    else if (emu_serial_mode == SERIAL_EMUMODE_GBP) {
      // Serial configured in slave mode, waiting for incoming word.
      if ((newval & 0x0080) && !(newval & 0x1) && !serial_irq_cycles) {
        // Send a new GBP sequence
        u32 rval = gbp_transfer(read_ioreg32(REG_SIODATA32_L));
        write_ioreg(REG_SIODATA32_L, rval & 0xFFFF);
        write_ioreg(REG_SIODATA32_H, rval >> 16);

        // Schedule the interrupt/reception. We simulate a 64KHz clock, which
        // translates to ~32 exchanges per frame (~2 rumble updates per frame).
        serial_irq_cycles = CLOCK_CYC_64KHZ_32BIT;
      }
    }
    else if (emu_serial_mode == SERIAL_EMUMODE_DISABLED) {
      // Simulate data TX, and its IRQ, since it should still work (even if it
      // makes zero sense). Some games might do this for some reason :D
      if ((newval & 0x0080) && !(newval & 0x1) && !serial_irq_cycles) {
        serial_irq_cycles = (newval & 0x2) ? CLOCK_CYC_2MHZ_8BIT :
                                             CLOCK_CYC_256KHZ_8BIT;
        if (newval & 0x1000)
          serial_irq_cycles <<= 2;
      }
    }
    break;
  case SERIAL_MODE_MULTI:
    // Multiplayer UART link emulation
    if (emu_serial_mode == SERIAL_EMUMODE_SERMULTI) {
      // Only parent can write the Start bit to initiate a transaction.
      if ((newval & 0x0080) && !(newval & 0x4) && !serial_irq_cycles) {
        // Send data request to slave devices, get back queued data
        //u16 rdata[4];
        lnk_master_send(read_ioreg(REG_SIOMLT_SEND));

        // Clear the receiving registers
        //write_ioreg(REG_SIOMULTI(0), rdata[0]);
        //write_ioreg(REG_SIOMULTI(1), rdata[1]);
        //write_ioreg(REG_SIOMULTI(2), rdata[2]);
        //write_ioreg(REG_SIOMULTI(3), rdata[3]);

        // serial_irq_cycles = uart_cycles[newval & 3];
        printf("Start TX (start bit)\n");
      }
    }
    else if (emu_serial_mode == SERIAL_EMUMODE_DISABLED) {

    }
    break;
  default:
    break;
  };

  // Update reg with its new value
  write_ioreg(REG_SIOCNT, newval);

  if (oldmode != newmode)
    set_serial_mode(newmode);

  return CPU_ALERT_NONE;
}

// How many cycles until the next serial event happens. Return MAX otherwise.
u32 serial_next_event() {
  if (serial_irq_cycles)
    return serial_irq_cycles;
  return ~0U;
}

// Account for consumed cycles and return if a serial IRQ should be raised.
bool update_serial(unsigned cycles) {
  // Might wanna check if the connected device has some update (IRQ).
  switch (emu_serial_mode) {
  case SERIAL_EMUMODE_RFU:
    if (rfu_update(cycles))
      return true;
    break;
  case SERIAL_EMUMODE_SERMULTI:
    if (lnk_update(cycles)) {
      printf("Raise IRQ serial\n");
    printf("Vals at raise  %x %x %x %x\n", read_ioreg(REG_SIOMULTI(0)), read_ioreg(REG_SIOMULTI(1)),
                    read_ioreg(REG_SIOMULTI(2)), read_ioreg(REG_SIOMULTI(3)));
      return true;
    }
    break;
  default:
    break;
  };

  if (serial_irq_cycles) {
    if (serial_irq_cycles > cycles)
      serial_irq_cycles -= cycles;
    else {
      // Event happening now!
      serial_irq_cycles = 0;
      printf("Serial IRQ raised : %d\n", (read_ioreg(REG_SIOCNT) & 0x4000) != 0);
      printf("Vals at raise %x %x %x %x\n", read_ioreg(REG_SIOMULTI(0)), read_ioreg(REG_SIOMULTI(1)),
                    read_ioreg(REG_SIOMULTI(2)), read_ioreg(REG_SIOMULTI(3)));
      // Clear the send bit, signal data is ready.
      // Set the device busy bit, to perform the weird SO/SI handshake.
      write_ioreg(REG_SIOCNT, read_ioreg(REG_SIOCNT) & ~0x80);
      // Return if IRQs are enabled.
      return read_ioreg(REG_SIOCNT) & 0x4000;
    }
  }

  return false;
}

