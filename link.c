/* gameplaySP
 *
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

// Debug print logic:
#define DEBUG_LINK 1
#ifdef DEBUG_LINK
  #define DEBUG_LINK_LOG(...) printf(__VA_ARGS__)
#else
  #define DEBUG_LINK_LOG(...)
#endif

// Unpacks big endian integers
static inline u32 upack32(const u8 *ptr) {
  return ptr[3] | (ptr[2] << 8) | (ptr[1] << 16) | (ptr[0] << 24);
}

// Track transaction numbers and peer data
/*static s64 lnk_trn_num;
static struct {
  s64 trn_num;
  u16 data;
} lnk_peer_data[4];*/

#define QUEUE_STATE_FILL       0  // Wait for the queue to fill a bit
#define QUEUE_STATE_PIPE       1  // Can pop elements out of the queue

#define QUEUE_HIGH_MARK        4

/*static struct {
  u8 state;
  u8 count;
  u16 queue[32];
} lnk_data[4];*/
static struct {
  u32 seqid;
  u16 value;
} lnk_data[4];
static u32 lnk_num_resp;

// Constants used for the network protocol.

#define NET_LNK_HEADER          0x4C4E4B31

#define NET_LNK_REQ           0x00    // Data broadcast to other peers
#define NET_LNK_RESP          0x01    // Data transaction (parent-mandated)

// Callbacks used to send and force-receive data.
void netpacket_send(uint16_t client_id, const void *buf, size_t len);
void netpacket_poll_receive();

static void lnk_net_send_data(u32 ptype, u32 seq, u32 info, u32 data) {
  u32 pkt[5] = {
    netorder32(NET_LNK_HEADER),  // LNK1 header
    netorder32(ptype),           // Message type
    netorder32(seq),
    netorder32(info),
    netorder32(data),
  };
  // All packets are broadcasted
  netpacket_send(0xffff, pkt, 20);
}

// This is called whenever the game uses the GPIO (pin D) to perform a reset
// pin flip in the external reset pin. We reset the device to a known state.
void lnk_reset() {
  DEBUG_LINK_LOG("LNK reset!\n");

  // Reset state machines
  memset(&lnk_data, 0, sizeof(lnk_data));
  lnk_num_resp = 0;

  // Reset registers to their default state
  write_ioreg(REG_SIOMULTI(0), 0xffff);
  write_ioreg(REG_SIOMULTI(1), 0xffff);
  write_ioreg(REG_SIOMULTI(2), 0xffff);
  write_ioreg(REG_SIOMULTI(3), 0xffff);
}

/*void lnk_master_send(u16 value, u16 *recvdata) {
  DEBUG_LINK_LOG("Send sync req %x\n", value);
  // Send the data, along with a sequence ID and the total number of clients.
  lnk_net_send_data(NET_LNK_REQ, lnk_seq_id++, netpl_num_clients, value);

  // "Receive" the value we just sent (this is actually important!)
  recvdata[0] = value;

  // Fill received data
  for (u32 i = 1; i < 4; i++) {
    if (lnk_data[i].state == QUEUE_STATE_PIPE && lnk_data[i].count) {
      recvdata[i] = lnk_data[i].queue[0];
      memmove(&lnk_data[i].queue[0], &lnk_data[i].queue[1],
              --lnk_data[i].count * sizeof(u16));
    } else {
      lnk_data[i].state = QUEUE_STATE_FILL;
      recvdata[i] = 0xffff;
    }
  }
}*/

void lnk_master_send(u16 value) {
  DEBUG_LINK_LOG("Send sync req %x (to %d cls)\n", value, netpl_num_clients); 
  // Send the data, along with a sequence ID and the total number of clients.
  lnk_data[0].value = value;
  lnk_data[0].seqid++;
  lnk_num_resp = netpl_num_clients;
  lnk_net_send_data(NET_LNK_REQ, lnk_data[0].seqid, netpl_num_clients, value);
}

/*bool lnk_update(unsigned cycles) {
  // Use this routine hook to schedule slave IRQs in a timely manner.
  u32 did = netpl_client_id & 3;
  if (lnk_slave_irq_lat)
    lnk_slave_irq_lat -= MIN(cycles, lnk_slave_irq_lat);

  if (did && !lnk_slave_irq_lat && lnk_data[did].count) {
    // We simulate slave reception at this moment (even though we do not
    // have the right data for other slaves). Usually means raising an IRQ.
    // This violates the principle that all devices get the same data (need
    // to check if this is actually super important or not).
    for (u32 i = 0; i < 4; i++) {
      if (lnk_data[i].state == QUEUE_STATE_PIPE && lnk_data[i].count) {
        write_ioreg(REG_SIOMULTI(i), lnk_data[i].queue[0]);
        memmove(&lnk_data[i].queue[0], &lnk_data[i].queue[1],
                --lnk_data[i].count * sizeof(u16));
      } else {
        lnk_data[i].state = QUEUE_STATE_FILL;
        write_ioreg(REG_SIOMULTI(i), 0xffff);
      }
    }
    lnk_slave_irq_lat = 11651; //CLOCK_CYC_115200B_4P;  TODO FIXME
    printf("Vals at raise slave %x %x %x %x\n", read_ioreg(REG_SIOMULTI(0)), read_ioreg(REG_SIOMULTI(1)),
                    read_ioreg(REG_SIOMULTI(2)), read_ioreg(REG_SIOMULTI(3)));

    // Only raise if the interrupt bit is actually enabled
    return read_ioreg(REG_SIOCNT) & 0x4000;
  }
  return false;
}*/

bool lnk_update(unsigned cycles) {
  if (!lnk_num_resp)
    return false;

  // We deliver the data once all clients and master are sync'ed
  u32 mid = lnk_data[0].seqid;
  for (u32 i = 1; i < lnk_num_resp; i++)
    if (lnk_data[i].seqid != mid)
      return false;

  // Write the IRQ result now
  for (u32 i = 0; i < 4; i++)
    write_ioreg(REG_SIOMULTI(i), 0xffff);
  for (u32 i = 0; i < lnk_num_resp; i++)
    write_ioreg(REG_SIOMULTI(i), lnk_data[i].value);

  // Update busy flag and perhaps raise IRQ
  write_ioreg(REG_SIOCNT, read_ioreg(REG_SIOCNT) & ~0x80);
  // Wipe this request not to raise it twice
  lnk_num_resp = 0;

  return read_ioreg(REG_SIOCNT) & 0x4000;
}

// Handles net packet reception.
void lnk_net_receive(const void* buf, size_t len, uint16_t client_id) {
  // LNK1 header, just some minor sanity check really.
  if (len == 20 && upack32((const u8*)buf) == NET_LNK_HEADER) {
    const u8 *buf8 = (const u8*)buf;
    u32 ptype = upack32(&buf8 [4]);
    u32 seqid = upack32(&buf8[ 8]);
    u32 info  = upack32(&buf8[12]);
    u32 data  = upack32(&buf8[16]);

    switch (ptype) {
    case NET_LNK_REQ:
      // Receive a serial transaction from the parent
      DEBUG_LINK_LOG("Got Req data: %x (seq: %d client: %d)\n", data, seqid, client_id);

      // Receive parent data
      if (client_id < 4) {
        lnk_data[client_id].value = data;
        lnk_data[client_id].seqid = seqid;
      }

      // Respond with our own data.
      if (netpl_client_id < 4) {
        u16 resp = read_ioreg(REG_SIOMLT_SEND);

        lnk_data[netpl_client_id].value = resp;
        lnk_data[netpl_client_id].seqid = seqid;

        // Parent tells us how many devices are connected.
        lnk_num_resp = info;

        DEBUG_LINK_LOG("Send Resp data %x (num cl %d)\n", resp, info);
        lnk_net_send_data(NET_LNK_RESP, seqid, 0, resp);
      }
      break;

    case NET_LNK_RESP:
      DEBUG_LINK_LOG("Got Resp data: %x (seq: %d client: %d)\n", data, seqid, client_id);
      // Store the data in the slot for later dispatch
      if (client_id < 4) {
        lnk_data[client_id].value = data;
        lnk_data[client_id].seqid = seqid;
      }
      break;
    };
  }
}

// Account for consumed cycles and return if a serial IRQ should be raised.
/*bool rfu_update(unsigned cycles) {
  if (rfu_comstate == RFU_COMSTATE_WAITEVENT) {
    // Force receive packets so that we can perhaps abort the wait
    // This helps minimize latency (othweise we need to wait a full frame!)
    netpacket_poll_receive();

    // Check if we are running our of time to respond.
    rfu_timeout_cycles -= MIN(cycles, rfu_timeout_cycles);
    rfu_resp_timeout   -= MIN(cycles, rfu_resp_timeout);

    // Wait for GBA to go into slave mode before finishing the wait!
    if ((read_ioreg(REG_SIOCNT) & 0x1) == 0) {
      if (rfu_data_avail()) {
        // Some event is available!
        rfu_buf[0] = 0x99660000 | RFU_CMD_RESP_DATA;
        rfu_buf[1] = 0x80000000;
        rfu_cnt = 0;
        rfu_plen = 2;
        rfu_comstate = RFU_COMSTATE_WAITRESP;
      }
      else if ((rfu_state == RFU_STATE_SHOST || rfu_state == RFU_STATE_HOST) &&
               !rfu_resp_timeout) {
        // We "retransmitted" the message N times (not really, but the equivalent
        // time has elapsed) and we simulate a lack of client response.
        rfu_buf[0] = 0x99660000 | RFU_CMD_RESP_DATA | (1 << 8);
        rfu_buf[1] = 0x00000F0F;  // TODO: just using 4 slots for now
        rfu_buf[2] = 0x80000000;
        rfu_cnt = 0;
        rfu_plen = 3;
        rfu_comstate = RFU_COMSTATE_WAITRESP;
      }
      else if ((rfu_state == RFU_STATE_SHOST || rfu_state == RFU_STATE_HOST) &&
               rfu_host.disc_flag) {
        // We are a host, and received a disconnect from a client.
        rfu_buf[0] = 0x99660000 | (1 << 8) | RFU_CMD_RESP_DISC;
        rfu_buf[1] = rfu_host.disc_flag;  // Reason disconnect (0)
        rfu_buf[2] = 0x80000000;
        rfu_cnt = 0;
        rfu_plen = 3;
        rfu_comstate = RFU_COMSTATE_WAITRESP;
        rfu_host.disc_flag = 0;
        RFU_DEBUG_LOG("Wait command resp: disconnect %x\n", rfu_host.disc_flag);
      }
      else if (!rfu_timeout_cycles) {
        // We ran out of time, just return an "error" code
        rfu_buf[0] = 0x99660000 | RFU_CMD_RESP_TIMEO;
        rfu_buf[1] = 0x80000000;
        rfu_cnt = 0;
        rfu_plen = 2;
        rfu_comstate = RFU_COMSTATE_WAITRESP;
        RFU_DEBUG_LOG("Wait command resp: timeout\n");
      }
    }
  }

  if (rfu_comstate == RFU_COMSTATE_WAITRESP) {
    // Pushes command and data as an RFU-master back to the GBA.
    // Only if SO/SI are low and the device is active to receive stuff
    if ((read_ioreg(REG_SIOCNT) & 0xC) == 0 && (read_ioreg(REG_SIOCNT) & 0x80)) {
      // Write data into the "received" register and clear active bit.
      write_ioreg(REG_SIODATA32_H, rfu_buf[rfu_cnt] >> 16);
      write_ioreg(REG_SIODATA32_L, rfu_buf[rfu_cnt] & 0xffff);
      write_ioreg(REG_SIOCNT, (read_ioreg(REG_SIOCNT) & ~0x80));
      rfu_cnt++;
      // Go back to slave mode
      if (rfu_cnt == rfu_plen)
        rfu_comstate = RFU_COMSTATE_WAITCMD;
      return read_ioreg(REG_SIOCNT) & 0x4000;
    }
  }

  return false;
}
*/
