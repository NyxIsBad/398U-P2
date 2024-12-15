#ifndef H_PRE
#define H_PRE

#include "arith.h"

// A linked list of Beaver triples [a], [b], [ab]
struct triple {
  struct triple *next;
  struct share *a;
  struct share *b;
  struct share *ab;
};

// A linked list of authenticated maliciously secure random shares [r], each
// associated with a wire. This should be used for generating shares of input.
struct randv {
  struct randv *next;
  char *wname;     // name of associated wire
  struct share *s; // authenticated share
  int is_value;    // if the value is set or not
  fp value;        // r (if applicable; ie wire is the user's input)
};

void init_preprocess(char *file);

#endif
