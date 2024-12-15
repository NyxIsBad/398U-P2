#include "msg.h"
#include "hosts.h"
#include <poll.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

fp packet_to_fp(packet *p) {
  fp f = be64toh(((uint64_t *)p->data)[0]);
  return f;
}

packet *fp_to_packet(fp elem) {
  uint64_t *buf = malloc(sizeof(char) * 8);
  buf[0] = htobe64(elem);
  packet *p = malloc(sizeof(packet));
  p->data = (uint8_t *)buf;
  p->len = 8;
  return p;
}

packet *to_packet(uint8_t *data, uint8_t len) {
  packet *p = malloc(sizeof(packet));
  p->data = data;
  p->len = len;
  return p;
}

void broadcast(struct host **conns, int num_conns, packet *data) {

  char *transmit = malloc(sizeof(char) * data->len + 1);
  transmit[0] = (char)data->len;
  memcpy((transmit + 1), data->data, data->len);
  for (int i = 0; i < num_conns; i++) {
    sendto(conns[i]->sockfd, transmit, data->len + 1, 0,
           (const struct sockaddr *)&conns[i]->conn, sizeof(conns[i]->conn));
  }
  free(transmit);
}

packet *recv_broadcasts(struct host **conns, int num_conns) {

  packet *packets = malloc(sizeof(packet) * num_conns);

  for (int i = 0; i < num_conns; i++) {
    packets[i].data = NULL;
    packets[i].len = 0;
  }

  for (int i = 0; i < num_conns; i++) {
    uint8_t *buf = malloc(sizeof(uint8_t) * 64);
    do {
      socklen_t len = sizeof(conns[i]->conn);
      recvfrom(conns[i]->sockfd, buf, 64, 0, (struct sockaddr *)&(conns[i]->conn),
               &len);
    } while (memcmp(buf, "\x04ping", 5) == 0 || memcmp(buf, "\x04""ackn", 5) == 0);
    uint8_t size = buf[0];
    packets[i].data = (buf + 1);
    packets[i].len = size;
  }

  return packets;
}

packet *recv_single_broadcast(struct host *con) {
  packet *p = malloc(sizeof(packet));
  p->data = NULL;
  p->len = 0;
  uint8_t *buf = malloc(sizeof(uint8_t) * 64);
  do {
    socklen_t len = sizeof(con->conn);
    recvfrom(con->sockfd, buf, 64, 0, (struct sockaddr *)&(con->conn), &len);
  } while (memcmp(buf, "\x04ping", 5) == 0 || memcmp(buf, "\x04""ackn", 5) == 0);
  uint8_t size = buf[0];
  p->data = (buf + 1);
  p->len = size;

  return p;
}
