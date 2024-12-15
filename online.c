#include "online.h"
#include "arith.h"
#include "circ.h"
#include "com.h"
#include "hosts.h"
#include "msg.h"
#include "pre.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// here we want to open a share:
// to do this, players
//  1. broadcast openings to plain shares
//  2. commit to mac candidate differences
//  3. open commitments
//  4. check the commitments; if they don't verify abort
//  5. if the sum is not 0, abort
fp secure_open(struct host **conns, int num_conns, fp delta, struct share *s) {
  // Suppose we are player 1
  // Step 1: Broadcast the plain share to everyone (this is x_1)
  packet *p = fp_to_packet(s->s);
  broadcast(conns, num_conns, p);
  // fprintf(stderr, "\nBroadcasted share: %lu\n", s->s);

  // Step 2: Commit to the mac candidate differences
  // Get player 2's plain share that they just broadcasted and compute the mac of it
  packet *recv_p = recv_broadcasts(conns, num_conns);
  fp *recv_shares = malloc(sizeof(fp) * num_conns);
  assert(recv_shares != NULL);
  // save the shares to recv_shares instead of recv_p
  for (int i = 0; i < num_conns; i++) {
    recv_shares[i] = packet_to_fp(&recv_p[i]);
    // fprintf(stderr, "recv_shares[%d]: %lu\n", i, recv_shares[i]);
  }

  // Now calculate x 
  fp x_prob = s->s;
  for (int i = 0; i < num_conns; i++) {
    // fprintf(stderr, "adding %lu to %lu\n  ", recv_shares[i], x_prob);
    x_prob = add(x_prob, recv_shares[i]);
  }
  // fprintf(stderr, "probable x: %lu\n", x_prob);

  // Compute the mac candidate differences (delta*x-t eg. d*x+(-t))
  fp mac_candidate_diff = add(mul(delta, x_prob), neg(s->s_mac));
  // DEBUGGING
  // fprintf(stderr, "mac_candidate_diff: %lu\n", mac_candidate_diff);
  fp rand_val = rand_fp();
  // fprintf(stderr, "rand_val: %lu\n", rand_val);
  // commit to it
  char *commitment = commit(mac_candidate_diff, rand_val);
  // broadcast the commitment
  packet *commitment_packet = to_packet((uint8_t *)commitment, 32);
  broadcast(conns, num_conns, commitment_packet);

  // Step 3: Open the commitments from player 2
  packet *recv_commitments = recv_broadcasts(conns, num_conns);

  // fprintf(stderr, "Sending commitment_pair[0]: %lu\n", mac_candidate_diff);
  packet *commitment_pair_packet = fp_to_packet(mac_candidate_diff);
  broadcast(conns, num_conns, commitment_pair_packet);
  // Receive everyone else's first commitment pair
  packet *recv_commitment_pairs_1 = recv_broadcasts(conns, num_conns);
  // fprintf(stderr, "Received commitment_pair[0]: %lu\n", packet_to_fp(&recv_commitment_pairs_1[0]));
  // fprintf(stderr, "Sending commitment_pair[1]: %lu\n", rand_val);
  commitment_pair_packet = fp_to_packet(rand_val);
  broadcast(conns, num_conns, commitment_pair_packet);
  // Receive everyone else's second commitment pair
  packet *recv_commitment_pairs_2 = recv_broadcasts(conns, num_conns);
  // fprintf(stderr, "Received commitment_pair[1]: %lu\n", packet_to_fp(&recv_commitment_pairs_2[0]));

  // Read the commitment pairs' d*x-t
  fp *commitment_pairs_1 = malloc(sizeof(fp) * num_conns);
  fp *commitment_pairs_2 = malloc(sizeof(fp) * num_conns);
  // fprintf(stderr, "num_conns: %d\n", num_conns);
  for (int i = 0; i < num_conns; i++) {
    commitment_pairs_1[i] = packet_to_fp(&recv_commitment_pairs_1[i]);
    commitment_pairs_2[i] = packet_to_fp(&recv_commitment_pairs_2[i]);
    // fprintf(stderr, "commitment_pairs: %lu, %lu\n", commitment_pairs_1[i], commitment_pairs_2[i]);
    check_open(commitment_pairs_1[i], commitment_pairs_2[i], (char *)recv_commitments[i].data);
  }

  // Step 5: Check the sum by summing together our commitment and everyone else's commitment
  fp sum = mac_candidate_diff;
  for (int i = 0; i < num_conns; i++) {
    sum = add(sum, commitment_pairs_1[i]);
  }
  assert(is_zero(sum));
  // fprintf(stderr, "Sum is zero, returning x_prob %lu\n", x_prob);
  // return the result
  return x_prob;
};

// Add a constant to a shared value [x] -> [x + c]
// a single arbitrary party should do the s -> s + c update: you may assume this
// party is named "p0"
// everyone updates macs!
struct share *const_add(struct share *s, fp constant, fp delta,
                        char *glob_name) {
  struct share *result = malloc(sizeof(struct share));
  assert(result != NULL);

  if (!strcmp(glob_name, "p0")) {
    // update the share
    result->s = add(s->s, constant);
  } else {
    result->s = s->s;
  }
  // update the mac
  result->s_mac = add(s->s_mac, mul(delta, constant));
  return result;
};

// Multiply a constant to a shared value [x] -> [cx]
struct share *const_mul(struct share *s, fp constant) {
  struct share *result = malloc(sizeof(struct share));
  assert(result != NULL);

  result->s = mul(s->s, constant);
  result->s_mac = mul(s->s_mac, constant);
  return result;
};

// Do a local share add ([x], [y]) -> [x + y]
struct share *local_add(struct share *s1, struct share *s2) {
  struct share *result = malloc(sizeof(struct share));
  assert(result != NULL);

  result->s = add(s1->s, s2->s);
  result->s_mac = add(s1->s_mac, s2->s_mac);
  return result;
};

// Do a local share sub ([x], [y]) -> [x - y]
struct share *local_sub(struct share *s1, struct share *s2) {
  // TODO: implement this
  // (not strictly necessary, but useful for mult)
  struct share *result = malloc(sizeof(struct share));
  assert(result != NULL);
  result->s = add(s1->s, neg(s2->s));
  result->s_mac = add(s1->s_mac, neg(s2->s_mac));
  return result;
};

// Use the opening and a triple to do a multiplication
// Do a multiplication ([x], [y]) -> [xy]
struct share *multiply(struct host **conns, int num_conns, fp delta,
                       char *glob_name, struct share *s1, struct share *s2,
                       struct triple *t) {
  // this uses beavers i think
  // va = s1, vb = s2
  // (d+a)=va, (e+b)=vb

  struct share *d = local_sub(s1, t->a); // (d+a)=va let this be d
  struct share *e = local_sub(s2, t->b); // and this e, in the textbook

  // fprintf(stderr, "d: %lu, e: %lu\n", d->s, e->s);
  // fprintf(stderr, "a: %lu, b: %lu, ab: %lu\n", t->a->s, t->b->s, t->ab->s);

  // fprintf(stderr, "Opening e and d on line 155\n");
  fp d_open = secure_open(conns, num_conns, delta, d);
  fp e_open = secure_open(conns, num_conns, delta, e);

  struct share *result = malloc(sizeof(struct share));
  assert(result != NULL);

//  fp c = t->ab->s;
  
  fp de = mul(d_open, e_open);
  // d[b] + e[a] + [ab] + de 
  struct share *db = const_mul(t->b, d_open); // d[b]
  struct share *ea = const_mul(t->a, e_open); // e[a]
  struct share *temp1 = local_add(db, ea); // d[b] + e[a]
  struct share *temp2 = local_add(temp1, t->ab); // d[b] + e[a] + [ab]
  result = const_add(temp2, de, delta, glob_name);

  return result;
};

// Arguments:
//      1. conns is the list of connections.  [ This is for broadcasting ].
//      2. num_conns is the number of connections.  [ For broadcasting ]
//      3. glob_name is the global name of you (the party).  [ For const add ]..
//      4. delta is the SPDZ global mac share.
//      5. g_wires is the global linked list of wires in eval order.
//      6. auth_rand is a list of random shares [r] (along with input vals)
//      7. auth_triples is a list of beaver triples [a], [b], [ab].
// Proceed through g_wires and evaluate each wire until you hit the end.
void spdz_online(struct host **conns, int num_conns, char *glob_name, fp delta,
                 struct wires *g_wires, struct randv *auth_rand,
                 struct triple *auth_triples) {
  // 1. loop through all the wires in the g_wires linked list
  //
  // 2. Check what operation is the wire from: do the operation (multiply, add)
  //          dont forget the edge case when one of the input wires is a
  //          constant!
  //
  // 3. (within the previous check): if the wire is input, use up an auth_rand
  // random share and produce shares of the input
  // 4. (within the previous check): if the wire is output, calculate it and
  // then at the end do a secure opening to find the output value.

  // DEBUGGING: running secure_open on the first config (preprocessing)
  /*// fprintf(stderr, "Testing with %lu", auth_rand->s->s);
  secure_open(conns, num_conns, delta, auth_rand->s);
  // fprintf(stderr, "Testing the mini functions\n");
  struct share *first = auth_rand->s;
  struct share *second = auth_rand->next->s;
  fp test_const = 5;
  // fprintf(stderr, "First: %lu, second: %lu\n", first->s, second->s);
  struct share *result = const_add(first, test_const, delta, glob_name);
  // fprintf(stderr, "const_add: %lu, mac: %lu\n", result->s, result->s_mac);
  result = const_mul(first, test_const);
  // fprintf(stderr, "const_mul: %lu, mac: %lu\n", result->s, result->s_mac);
  result = local_add(first, second);
  // fprintf(stderr, "local_add: %lu, mac: %lu\n", result->s, result->s_mac);
  result = local_sub(first, second);
  // fprintf(stderr, "local_sub: %lu, mac: %lu\n", result->s, result->s_mac);
  // fprintf(stderr, "Testing multiply\n");
  struct triple *t = auth_triples;
  struct share *result = multiply(conns, num_conns, delta, glob_name, first, second, t);
  // fprintf(stderr, "multiply: %lu, mac: %lu\n", result->s, result->s_mac);

  // fprintf(stderr, "%lu\n", add(18446744073709551461ULL, 18446744073709551246ULL));
  // fprintf(stderr, "%lu\n", add(18446744073709551535ULL, 18446744073709551491ULL));
  // fprintf(stderr, "%lu\n", add(2022ULL, 18446744073709551135ULL));

  return;*/
  // fprintf(stderr, "1");
  struct wires *current = g_wires;
  // fprintf(stderr, "2");
  while (current != NULL) {
    struct wire *w = current->w;
    // fprintf(stderr, "3");
    switch(w->operation) {
      case 2: { // Input
        // fprintf(stderr, "input\n");
        struct randv *r = auth_rand;
        // find the right auth_rand
        while (strcmp(r->wname, w->wname)) {
          r = r->next;
          if (r == NULL) {
            // fprintf(stderr, "Error: could not find the right auth_rand\n");
            exit(1);
          }
        }

        // create a share for the input
        w->share = malloc(sizeof(struct share));
        assert(w->share != NULL);
        /*
        r->s: [r] [*share]
        r->value: r [fp]
        w->val: x [fp]
        */
        // delta = x-r
        // announce delta to parties if we are the user
        fp del = 0;
        // if we are the owner of the wire
        if (!strcmp(glob_name, w->input_name)) {
          // fprintf(stderr, "BROADCASTING THING\n");
          // then find delta and broadcast it
          // d=x-r
          del = add(w->val, neg(r->value));
          packet *del_packet = fp_to_packet(del);
          broadcast(conns, num_conns, del_packet);
        } else {
          // else look for the owner of the wire
          // and receive delta
          // fprintf(stderr, "RECEIVING THING\n");
          for (int i = 0; i < num_conns; i++) {
            if (!strcmp(conns[i]->name, w->input_name)) {
              packet *del_packet = recv_single_broadcast(conns[i]);
              del = packet_to_fp(del_packet);
              break;
            }
          }
        }
        // calculate share to be [x]=[r]+d
        w->share = const_add(r->s, del, delta, glob_name);
        // fprintf(stderr, "Share is %lu\n", w->share->s);
        break;
      }
      case 0: { // Add
        // fprintf(stderr, "input\n");
        // check for constants
        if ((w->in1->operation == 3) && (w->in2->operation == 3)) {
          w->val = add(w->in1->val, w->in2->val);
          w->operation = 3;
        } else if (w->in1->operation == 3) {
          w->share = const_add(w->in2->share, w->in1->val, delta, glob_name);
        } else if (w->in2->operation == 3) {
          w->share = const_add(w->in1->share, w->in2->val, delta, glob_name);
        } else {
          w->share = local_add(w->in1->share, w->in2->share);
        }
        break;
      }
      case 1: { // Multiply
        // fprintf(stderr, "multiply\n");
        // check for constants
        if ((w->in1->operation == 3) && (w->in2->operation == 3)) {
          w->val = mul(w->in1->val, w->in2->val);
          w->operation = 3;
        } else if (w->in1->operation == 3) {
          w->share = const_mul(w->in2->share, w->in1->val);
        } else if (w->in2->operation == 3) {
          w->share = const_mul(w->in1->share, w->in2->val);
        } else {
          w->share = multiply(conns, num_conns, delta, glob_name, w->in1->share, w->in2->share, auth_triples);
          auth_triples = auth_triples->next;
        }
        break;
      }
      case 3: { // Constant
        // fprintf(stderr, "constant\n");
        w->share = malloc(sizeof(struct share));
        assert(w->share != NULL);
        w->share->s = w->val;
        w->share->s_mac = mul(delta, w->val);
        break;
      }
    }
    // fprintf(stderr, "4");
    if (w->is_output) {
      // secure open the output
      // fprintf(stderr, "Opening output on line 239\n");
      fp res = secure_open(conns, num_conns, delta, w->share);
      printf("Output: %lu\n", get_output(res));
    }
    current = current->next;
  }
}
