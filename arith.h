
#ifndef H_ARITH
#define H_ARITH

#include <stdint.h>

// typedef struct {
//   uint64_t val;
// } fp;

// Field element (invariant: val <= MOD)
typedef uint64_t fp;

// An authenticated share: consists of linear shares of (x, Delta * x)
struct share {
  fp s;
  fp s_mac;
};

// Generate a fully random field element
fp rand_fp();

// Convert a uint to a Fp
fp from(uint64_t v);

// Add two field elements together
fp add(fp a, fp b);

// Multiply two field elements together
fp mul(fp a, fp b);

// Negate a field element (-x)
fp neg(fp a);

// Check if a field element is zero.
int is_zero(fp x);

// Produce a printable uint64 from the field element.
uint64_t get_output(fp o);

#endif
