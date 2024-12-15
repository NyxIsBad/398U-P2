#include "arith.h"
#include <stdio.h>
#include <stdlib.h>

// Field: 18446744073709551557

const uint64_t MOD = 18446744073709551557ULL;

fp rand_fp() {
  uint64_t v = ((uint64_t)rand() << 32) | ((uint64_t)rand());
  v = v % MOD;
  fp x = v;
  return x;
}

fp from(uint64_t v) {
  fp x = v % MOD;
  return x;
}

fp add(fp a, fp b) {
  fp x = (a + b);
  if (x > MOD || (x < a && x < b)) {
    x -= MOD;
  }
  x %= MOD;
  return x;
}

fp mul(fp a, fp b) {
  uint64_t v = b;
  uint64_t r = a;
  uint64_t o = 0;
  while (v > 0) {
    if (v % 2 == 1) {
      uint64_t tmp = o + r;
      if (tmp > MOD || (tmp < o && tmp < r)) {
        tmp -= MOD;
      }
      o = tmp % MOD;
    }
    // r + r
    uint64_t tmp = r + r;
    if (tmp > MOD || (tmp < r)) {
      tmp -= MOD;
    }
    r = tmp % MOD;

    v >>= 1;
  }
  o = o % MOD;
  fp x = o;
  return x;
}

fp neg(fp a) {
  fp x = MOD - a;
  return x;
}

int is_zero(fp x) { return (x == 0); }

uint64_t get_output(fp x) { return x; }
