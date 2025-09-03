/* gameplaySP
 *
 * Copyright (C) 2025 David Guillen Fandos <david@davidgf.net>
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

// Here we emulate certain serial protocols to allow for netplay.
// Since real link cable emulation is very hard, here we partially emulate
// the other devices (GBAs) and using some fake data and real data
// recreate some serial protocols.

#include "common.h"

// Debug print logic:
//#define SERIALPROTO_DEBUG 1
#ifdef SERIALPROTO_DEBUG
  #define SRPT_DEBUG_LOG(...) printf(__VA_ARGS__)
#else
  #define SRPT_DEBUG_LOG(...)
#endif


// Serial-Poke: emulates (via fakes) the pokemon serial protocol.
//
// The protocol has two phases: handshake and data exchange.
// During handshake clients are discovered using magic constants.
// Data exchange uses some frame format (1+8 half-words) to exchange data
// with some relaxed rules on latency. Frames must start with a checksum
// word followed by 8 data words.
// For masters we simulate some empty frames when no data is available,
// for slaves we simulate a fake master at a rate of 9 irqs / frame.

#define NET_SERPOKE_HEADER          0x4d504b31   // MPK1 (Multiplayer Pokemon)

// Internal states
#define STATE_PREINIT        0
#define STATE_HANDSHAKE      1
#define STATE_CONNECTED      2

#define SEQ_HANDSHAKE_TOKENS   18
#define SLAVE_IRQ_CYCLES       28672 // Aproximately every 1.7ms, ~9.5 per frame.

#define MAX_QPACK             128    // 1 packet per frame (~2 second buffer, maybe too big)

// Pokemon protocol constants
#define MASTER_HANDSHAKE    0x8FFF
#define SLAVE_HANDSHAKE     0xB9A0

void netpacket_send(uint16_t client_id, const void *buf, size_t len);

// Unpacks big endian integers used for signaling
static inline u32 upack32(const u8 *ptr) {
  return ptr[3] | (ptr[2] << 8) | (ptr[1] << 16) | (ptr[0] << 24);
}

int ismemzero(const void *ptr, size_t bytes) {
  const uint8_t *p = (uint8_t*)ptr;
  while (bytes--) {
    if (*p++)
      return 0;
  }
  return 1;
}

static struct {
  struct {
    uint16_t data[MAX_QPACK][8];
    uint16_t state;
    uint8_t count;             // Number of queued packets
    uint8_t recvd;             // Whether we are sending any data
  } peer[4];                   // One of them not used really

  uint16_t checksum;
  uint8_t offset;              // Current frame offset
  uint8_t hscnt;               // Number of handshake tokens sent
  unsigned frcnt;              // Frame counter for events.
} serialpoke_state;

void serialpoke_reset(void) {
  SRPT_DEBUG_LOG("Reset serial-poke state\n");
  memset(&serialpoke_state, 0, sizeof(serialpoke_state));
}

static void serialpoke_senddata(uint16_t state, const uint16_t *packet) {
  u32 i;
  uint32_t flags = state | (packet ? 0x80000000 : 0);
  u32 pkt[10] = {
    netorder32(NET_SERPOKE_HEADER),  // Header magic
    netorder32(flags),               // Current device state
  };
  for (i = 0; i < 8; i++)
    pkt[i+2] = packet ? netorder32(packet[i]) : 0;

  netpacket_send(RETRO_NETPACKET_BROADCAST, pkt, sizeof(pkt));
}

// Called when serial master schedules a serial transfer.
void serialpoke_master_send(void) {
  u32 i;
  u16 mvalue = read_ioreg(REG_SIOMLT_SEND);

  write_ioreg(REG_SIOMULTI0, mvalue);   // echo sent value

  if (serialpoke_state.peer[0].state == STATE_PREINIT) {
    if (mvalue == SLAVE_HANDSHAKE) {
      // Move to state handshake. Signal that to peers.
      serialpoke_state.peer[0].state = STATE_HANDSHAKE;
      for (i = 1; i <= 3; i++)
        write_ioreg(REG_SIOMULTI0 + i, 0);
      // Send new state to peers.
      serialpoke_senddata(serialpoke_state.peer[0].state, NULL);
    }
  }
  else if (serialpoke_state.peer[0].state == STATE_HANDSHAKE) {
    // Check if our peers are ready.
    for (i = 1; i <= 3; i++)
      write_ioreg(REG_SIOMULTI0 + i,
        serialpoke_state.peer[i].state == STATE_HANDSHAKE ? SLAVE_HANDSHAKE : 0xFFFF);

    // Move to connection state.
    if (mvalue == MASTER_HANDSHAKE) {
      SRPT_DEBUG_LOG("Master handshake detected, moving to connected mode!\n");
      serialpoke_state.peer[0].state = STATE_CONNECTED;
      serialpoke_state.checksum = 0;
      serialpoke_state.offset = 0;
      serialpoke_state.hscnt = 0;
      for (i = 1; i <= 3; i++)
        serialpoke_state.peer[i].count = 0;    // Drop data packets
    }

    // Keeps sending updates really.
    serialpoke_senddata(serialpoke_state.peer[0].state, NULL);
  } else {
    // Detect if we are trying to re-start a handshake, a bit rough.
    if (mvalue != SLAVE_HANDSHAKE)
      serialpoke_state.hscnt = 0;
    else {
      if (++serialpoke_state.hscnt > SEQ_HANDSHAKE_TOKENS) {
        SRPT_DEBUG_LOG("Detected handshake, switching state!\n");
        serialpoke_state.peer[0].state = STATE_HANDSHAKE;
        return;
      }
    }

    // 1 checksum word, then 8 data words.
    if (serialpoke_state.offset == 0) {
      for (i = 1; i <= 3; i++) {
        write_ioreg(REG_SIOMULTI0 + i, serialpoke_state.checksum);
        // Check whether there's a packet ready to be transferred.
        serialpoke_state.peer[i].recvd = serialpoke_state.peer[i].count > 0;
      }
      serialpoke_state.offset++;
      serialpoke_state.checksum = 0;
    }
    else {
      serialpoke_state.peer[0].data[0][serialpoke_state.offset-1] = mvalue;
      serialpoke_state.checksum += mvalue;

      for (i = 1; i <= 3; i++) {
        if (serialpoke_state.peer[i].recvd) {
          u16 w = serialpoke_state.peer[i].data[0][serialpoke_state.offset-1];
          serialpoke_state.checksum += w;
          write_ioreg(REG_SIOMULTI0 + i, w);
        }
        else
          write_ioreg(REG_SIOMULTI0 + i, 0);
      }

      if (serialpoke_state.offset++ >= 8) {
        // Send packet data
        if (ismemzero(serialpoke_state.peer[0].data[0], sizeof(serialpoke_state.peer[0].data[0]))) {
          SRPT_DEBUG_LOG("Skip empty frame, just sending status instead.\n");
          serialpoke_senddata(STATE_CONNECTED, NULL);
        } else {
          SRPT_DEBUG_LOG("Sending packet as master [%04x, %04x, ...]\n",
                         serialpoke_state.peer[0].data[0][0], serialpoke_state.peer[0].data[0][1]);
          serialpoke_senddata(STATE_CONNECTED, serialpoke_state.peer[0].data[0]);
        }

        serialpoke_state.offset = 0;
        // Consume data packet.
        for (i = 1; i <= 3; i++) {
          if (serialpoke_state.peer[i].recvd) {
            if (--serialpoke_state.peer[i].count) {
              memmove(serialpoke_state.peer[i].data[0],
                      serialpoke_state.peer[i].data[1],
                      serialpoke_state.peer[i].count * 8 * sizeof(uint16_t));
            }
          }
        }
      }
    }
  }
}


bool serialpoke_update(unsigned cycles) {
  u32 i;
  serialpoke_state.frcnt += cycles;

  // Raise an IRQ periodically to pretend there's a master.
  if (netplay_client_id && serialpoke_state.frcnt > SLAVE_IRQ_CYCLES) {
    serialpoke_state.frcnt = 0;

    // We simply copy the send register to our reception register for consistency.
    write_ioreg(REG_SIOMULTI0 + netplay_client_id, read_ioreg(REG_SIOMLT_SEND));

    // Check which state the master is in and try to act accordingly.
    if (serialpoke_state.peer[0].state == STATE_PREINIT)
      return false; // Does nothing, no data will be sent.

    else if (serialpoke_state.peer[0].state == STATE_HANDSHAKE) {
      // Move the client to the PREINIT state, then to HANDSHAKE if it replies correctly.
      serialpoke_state.peer[netplay_client_id].state = STATE_PREINIT;
      // Check if the client wants to send a handshake.
      if (read_ioreg(REG_SIOMLT_SEND) == SLAVE_HANDSHAKE)
        // Move the HANDSHAKE state!
        serialpoke_state.peer[netplay_client_id].state = STATE_HANDSHAKE;

      // Emulate other values (either handshake or zero should do it).
      for (i = 0; i <= 3; i++)
        if (i != netplay_client_id)
          write_ioreg(REG_SIOMULTI0 + i,
            serialpoke_state.peer[i].state == STATE_HANDSHAKE ? SLAVE_HANDSHAKE : 0xFFFF);

      // Simply send updates periodically to inform about our state.
      serialpoke_senddata(serialpoke_state.peer[netplay_client_id].state, NULL);
      return true;
    }
    else {
      // Connected mode, if we are still in handshake, simulate a MASTER sync
      if (serialpoke_state.peer[netplay_client_id].state == STATE_HANDSHAKE) {
        SRPT_DEBUG_LOG("Triggering IRQ for master handshake (handshake->connected).\n");
        serialpoke_state.peer[netplay_client_id].state = STATE_CONNECTED;
        serialpoke_state.checksum = 0;
        serialpoke_state.offset = 0;
        serialpoke_state.hscnt = 0;

        write_ioreg(REG_SIOMULTI0, MASTER_HANDSHAKE);
        for (i = 1; i <= 3; i++)
          if (i != netplay_client_id)
            write_ioreg(REG_SIOMULTI0 + i,
              serialpoke_state.peer[i].state == STATE_HANDSHAKE ? SLAVE_HANDSHAKE : 0xFFFF);

        serialpoke_senddata(serialpoke_state.peer[netplay_client_id].state, NULL);
        return true;
      }
      else if (serialpoke_state.peer[netplay_client_id].state == STATE_CONNECTED) {
        u16 nw = read_ioreg(REG_SIOMLT_SEND);

        if (nw != SLAVE_HANDSHAKE)
          serialpoke_state.hscnt = 0;
        else {
          if (++serialpoke_state.hscnt > SEQ_HANDSHAKE_TOKENS) {
            serialpoke_state.peer[netplay_client_id].state = STATE_HANDSHAKE;
            return false;
          }
        }

        if (serialpoke_state.offset == 0) {
          for (i = 0; i <= 3; i++) {
            if (i == netplay_client_id)
              serialpoke_state.peer[i].count = 1;

            write_ioreg(REG_SIOMULTI0 + i, serialpoke_state.checksum);
            // Check whether there's a packet ready to be transferred.
            serialpoke_state.peer[i].recvd = serialpoke_state.peer[i].count > 0;
            SRPT_DEBUG_LOG("Client %d has %d pending packets\n", i, serialpoke_state.peer[i].count);
          }
          serialpoke_state.checksum = 0;
          serialpoke_state.offset++;
        }
        else {
          serialpoke_state.peer[netplay_client_id].data[0][serialpoke_state.offset-1] = nw;

          for (i = 0; i <= 3; i++) {
            if (serialpoke_state.peer[i].recvd) {
              u16 w = serialpoke_state.peer[i].data[0][serialpoke_state.offset-1];
              write_ioreg(REG_SIOMULTI0 + i, w);
              serialpoke_state.checksum += w;
            }
            else
              write_ioreg(REG_SIOMULTI0 + i, 0);
          }

          if (serialpoke_state.offset++ >= 8) {
            // Send packet data
            if (ismemzero(serialpoke_state.peer[netplay_client_id].data[0],
                          sizeof(serialpoke_state.peer[netplay_client_id].data[0]))) {
              SRPT_DEBUG_LOG("Skip empty frame, just sending status instead.\n");
              serialpoke_senddata(STATE_CONNECTED, NULL);
            } else {
              SRPT_DEBUG_LOG("Sending packet as slave [%04x, %04x, ...]\n",
                             serialpoke_state.peer[netplay_client_id].data[0][0],
                             serialpoke_state.peer[netplay_client_id].data[0][1]);
              serialpoke_senddata(STATE_CONNECTED, serialpoke_state.peer[netplay_client_id].data[0]);
            }

            serialpoke_state.offset = 0;
            for (i = 0; i <= 3; i++) {
              if (serialpoke_state.peer[i].recvd) {
                if (--serialpoke_state.peer[i].count)
                  memmove(serialpoke_state.peer[i].data[0],
                          serialpoke_state.peer[i].data[1],
                          serialpoke_state.peer[i].count * 8 * sizeof(uint16_t));
              }
            }
          }
        }
        return true;
      }
    }
  }
  return false;
}

void serialpoke_net_receive(const void* buf, size_t len, uint16_t client_id) {
  // MPK1 header, sanity checking.
  u32 i;
  if (len == 40 && upack32((const u8*)buf) == NET_SERPOKE_HEADER) {
    const uint32_t *pkt = (uint32_t*)buf;
    const unsigned count = serialpoke_state.peer[client_id].count;
    const u32 flags = netorder32(pkt[1]);

    serialpoke_state.peer[client_id].state = flags & 0xFFFF;
    SRPT_DEBUG_LOG("Received valid packet from client %d (state: %d)\n",
                   client_id, serialpoke_state.peer[client_id].state);

    if ((flags & 0x80000000) && count < MAX_QPACK) {
      for (i = 0; i < 8; i++)
        serialpoke_state.peer[client_id].data[count][i] = netorder32(pkt[i+2]);
      serialpoke_state.peer[client_id].count++;
    }
    else if ((flags & 0x80000000)) {
      SRPT_DEBUG_LOG("Packet dropped!\n");
    }
  }
}


