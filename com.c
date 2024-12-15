#include "com.h"
#include "arith.h"
#include <assert.h>
#include <openssl/sha.h>
#include <stdlib.h>

char *commit(fp data, fp random) {
  char inp_data[16];
  char *outbuf = malloc(32 * sizeof(char));
  for (int i = 0; i < 32; i++) {
    outbuf[i] = 0;
  }
  ((uint64_t *)inp_data)[0] = data;
  ((uint64_t *)inp_data)[1] = random;
  SHA256((unsigned char *)inp_data, 16, (unsigned char *)outbuf);
  return outbuf;
}

void check_open(fp data, fp random, char *commitment) {
  char inp_data[16];
  char *outbuf = malloc(32 * sizeof(char));
  for (int i = 0; i < 32; i++) {
    outbuf[i] = 0;
  }
  ((uint64_t *)inp_data)[0] = data;
  ((uint64_t *)inp_data)[1] = random;
  SHA256((unsigned char *)inp_data, 16, (unsigned char *)outbuf);
  for (int i = 0; i < 32; i++) {
    assert(outbuf[i] == commitment[i]);
  }
}
