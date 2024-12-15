#ifndef H_MSG
#define H_MSG

#include "arith.h"
#include "hosts.h"
#include <stdint.h>

typedef struct {
  uint8_t *data;
  uint8_t len;
} packet;

// Convert a packet (recieved on the network) into a field element.
fp packet_to_fp(packet *p);

// Convert a field element to a packet.
packet *fp_to_packet(fp elem);

// Convert a char [len] array into a packet.
// Note: this is necessary for the commitments sent.
packet *to_packet(uint8_t *data, uint8_t len);

// Broadcast to all connections a packet.
void broadcast(struct host **conns, int num_conns, packet *data);

// Recieve from all connections a packet.
packet *recv_broadcasts(struct host **conns, int num_conns);

// Recieve from a single connection a packet. (Can use it for recieving the
// initial input opening for wires).
packet *recv_single_broadcast(struct host *con);

#endif
