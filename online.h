
#ifndef H_ONL
#define H_ONL

#include "arith.h"
#include "circ.h"
#include "hosts.h"
#include "pre.h"

void spdz_online(struct host **conns, int num_conns, char *glob_name,
                 fp mac_share, struct wires *g_wires, struct randv *auth_rand,
                 struct triple *auth_triples);

#endif
