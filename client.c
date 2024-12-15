#include "circ.h"
#include "hosts.h"
#include "online.h"
#include "parse.h"
#include "pre.h"
#include <poll.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

extern char *f_host; // host filename (ignore)
extern char *f_circ; // circuit filename (ignore)
extern char *f_pre;  // preprocess filename (ignore)

extern struct host *conns[1024]; // external connections to other parties
extern int num_conns;            // number of total connections
extern char *glob_name;          // global ident for this party

extern fp delta;

extern struct wires *g_wires; // circuit wires stored linearly (order matters!)

extern struct randv *auth_rand;     // authenticated randomness (ie; malicious
                                    // secret shares of random values)
extern struct triple *auth_triples; // authenticated triples (ie; malicious
                                    // secret shares of a, b, ab)

void initialize() {
  init_hosts(f_host);
  init_circuit(f_circ);
  init_preprocess(f_pre);

  printf("\n\n\n --- CONNECTIONS --- \n\n");
  for (int i = 0; i < num_conns; i++) {
    printf("Connected with %s:%d at %d\n", conns[i]->name, conns[i]->c_port,
           conns[i]->h_port);
  }

  printf("\n --- PREPROCESSING --- \n\n");

  printf("GLOBAL MAC SHARE: [%lu]\n", delta);

  struct triple *t;
  for (t = auth_triples; t != NULL; t = t->next) {
    printf("TRIPLE [a] = (%lu %lu) [b] = (%lu %lu) [c] = (%lu %lu)\n", t->a->s,
           t->a->s_mac, t->b->s, t->b->s_mac, t->ab->s, t->ab->s_mac);
  }

  struct randv *r;

  for (r = auth_rand; r != NULL; r = r->next) {
    printf("RAND [r] = (%lu %lu)", r->s->s, r->s->s_mac);
    if (r->is_value != 0) {
      printf(" (r = %lu)\n", r->value);
    } else {
      printf("\n");
    }
  }

  printf("\n --- WIRES --- \n\n");

  struct wires *a;

  for (a = g_wires; a != NULL; a = a->next) {
    if (a->w->operation == 2) {
      printf("INPUT WIRE BY [%s] ", a->w->input_name);
      if (strcmp(a->w->input_name, glob_name) == 0) {
        printf("(i = %lu)\n", a->w->val);
      } else {
        printf("\n");
      }
    }
  }
}

uint8_t check_arr(uint8_t *ready, int len) {
  for (int i = 0; i < len; i++) {
    if (((ready[i] & 1) == 0) || ((ready[i] & 2) == 0)) {
      return 0;
    }
  }
  return 1;
}

void wait_for_connections() {

  printf("\n\n\n --- PHASE 1 --- \n\n\n");

  printf("Waiting for connections...\n");

  struct pollfd *fds = malloc(sizeof(struct pollfd) * num_conns);

  uint8_t *is_ready = malloc(sizeof(uint8_t) * num_conns);
  for (int i = 0; i < num_conns; i++) {
    is_ready[i] = 0;
  }

  while (check_arr(is_ready, num_conns) == 0) {
    int numfds = 0;
    // send out a ping to all hosts, and wait 10 seconds for an ack
    char pepega[5] = {'\x04', 'p', 'i', 'n', 'g'};
    for (int i = 0; i < num_conns; i++) {
      if ((is_ready[i] & 1) == 0) {
        printf("Pinging %s\n", conns[i]->name);
        sendto(conns[i]->sockfd, pepega, 5, 0,
               (const struct sockaddr *)&conns[i]->conn,
               sizeof(conns[i]->conn));
        fds[numfds].fd = conns[i]->sockfd;
        fds[numfds].events = POLLIN;
        fds[numfds].revents = 0;
        numfds += 1;
      } else if ((is_ready[i] & 2) == 0) {
        fds[numfds].fd = conns[i]->sockfd;
        fds[numfds].events = POLLIN;
        fds[numfds].revents = 0;
        numfds += 1;
      }
    }

    int out = poll(fds, numfds, 10000);

    if (out > 0) {
      for (int i = 0; i < numfds; i++) {
        if (fds[i].revents > 0) {
          int connid = 0;
          for (int j = 0; j < num_conns; j++) {
            if (conns[j]->sockfd == fds[i].fd) {
              connid = j;
            }
          }

          unsigned char buf[5] = {0};
          socklen_t len = sizeof(conns[connid]->conn);
          recvfrom(fds[i].fd, buf, 5, 0,
                   (struct sockaddr *)&(conns[connid]->conn), &len);

          if (buf[0] == '\x04' && buf[1] == 'p' && buf[2] == 'i' &&
              buf[3] == 'n' && buf[4] == 'g') {
            printf("Received ping from %s, acking\n", conns[connid]->name);
            char omega[5] = {'\x04', 'a', 'c', 'k', 'n'};
            sendto(fds[i].fd, omega, 5, 0,
                   (const struct sockaddr *)&conns[connid]->conn,
                   sizeof(conns[connid]->conn));
            is_ready[connid] |= 2;
          } else if (buf[0] == '\x04' && buf[1] == 'a' && buf[2] == 'c' &&
                     buf[3] == 'k' && buf[4] == 'n') {
            printf("Received ack from %s\n", conns[connid]->name);
            is_ready[connid] |= 1;
          }
        }
      }
    }
  }

  free(is_ready);

  sleep(5);
}

int main(int argc, char **argv) {
  srand(time(NULL));
  parse(argc, argv);

  printf("Got host file: %s\n", f_host);
  printf("Got circuit file: %s\n", f_circ);
  printf("Got preprocessing file: %s\n\n\n", f_pre);

  initialize();

  wait_for_connections();

  printf("\n\n\n --- PHASE 2 ---\n\n\n");

  spdz_online(conns, num_conns, glob_name, delta, g_wires, auth_rand,
              auth_triples);
}
