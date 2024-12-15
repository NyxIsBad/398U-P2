#include "pre.h"
#include "circ.h"
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct randv *auth_rand;
struct triple *auth_triples;

fp delta;

void init_preprocess(char *file) {
  char *line = NULL;
  size_t len = 0;
  ssize_t read;

  auth_rand = NULL;
  auth_triples = NULL;

  FILE *fp = fopen(file, "r");
  if (fp == NULL) {
    printf("Preprocessing file not found.\n");
    exit(1);
  }

  while ((read = getline(&line, &len, fp)) != -1) {
    char *wname = malloc(200 * sizeof(char));
    uint64_t share;
    uint64_t share_mac;
    uint64_t val;
    int ret = sscanf(line, "rand %200s (%lu, %lu) %lu", wname, &share,
                     &share_mac, &val);
    if (ret == 4) {
      struct randv *rand_value = malloc(sizeof(struct randv));
      rand_value->wname = wname;
      rand_value->next = auth_rand;
      rand_value->s = malloc(sizeof(struct share));
      rand_value->s->s = from(share);
      rand_value->s->s_mac = from(share_mac);
      rand_value->is_value = 1;
      rand_value->value = from(val);
      auth_rand = rand_value;
    } else if (ret == 3) {
      struct randv *rand_value = malloc(sizeof(struct randv));
      rand_value->wname = wname;
      rand_value->next = auth_rand;
      rand_value->s = malloc(sizeof(struct share));
      rand_value->s->s = from(share);
      rand_value->s->s_mac = from(share_mac);
      rand_value->is_value = 0;
      rand_value->value = 0;
      auth_rand = rand_value;
    } else {
      uint64_t share_a;
      uint64_t share_mac_a;
      uint64_t share_b;
      uint64_t share_mac_b;
      uint64_t share_ab;
      uint64_t share_mac_ab;
      int ret = sscanf(line, "triple (%lu, %lu) (%lu, %lu) (%lu, %lu)",
                       &share_a, &share_mac_a, &share_b, &share_mac_b,
                       &share_ab, &share_mac_ab);
      if (ret == 6) {
        struct triple *tp = malloc(sizeof(struct triple));
        tp->next = auth_triples;
        tp->a = malloc(sizeof(struct share));
        tp->a->s = from(share_a);
        tp->a->s_mac = from(share_mac_a);
        tp->b = malloc(sizeof(struct share));
        tp->b->s = from(share_b);
        tp->b->s_mac = from(share_mac_b);
        tp->ab = malloc(sizeof(struct share));
        tp->ab->s = from(share_ab);
        tp->ab->s_mac = from(share_mac_ab);
        auth_triples = tp;
      } else {
        uint64_t macv;
        int mac = sscanf(line, "mac %lu", &macv);
        if (mac == 1) {
          delta = from(macv);
        }
      }
    }
  }
}
