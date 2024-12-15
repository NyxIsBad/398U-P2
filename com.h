
#ifndef H_COM
#define H_COM

#include "arith.h"
#include <openssl/sha.h>

// Produces a char[32] 32 byte array with the commitment contained within.
// NOTE: IT IS 32 BYTES EXACTLY.
char *commit(fp data, fp random);

// Checks the opening of a 32 byte commitment (makes commitment correctly bound
// data).
void check_open(fp data, fp random, char *commitment);

#endif
