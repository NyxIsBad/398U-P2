#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

extern char *optarg;
char *f_pre;
char *f_host;
char *f_circ;

int parse(int argc, char **argv) {
  char opt;
  bool h;
  bool c;
  bool p;

  while ((opt = getopt(argc, argv, "h:c:p:")) != EOF) {
    switch (opt) {
    case 'h':
      f_host = optarg;
      h = true;
      break;
    case 'c':
      f_circ = optarg;
      c = true;
      break;
    case 'p':
      f_pre = optarg;
      p = true;
      break;
    }
  }

  if (!h) {
    printf("Please provide all arguments.\n");
    exit(1);
  }

  if (!c) {
    printf("Please provide all arguments.\n");
    exit(1);
  }

  if (!p) {
    printf("Please provide all arguments.\n");
    exit(1);
  }

  return optind;
}
