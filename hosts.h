#ifndef H_HOST
#define H_HOST

#include <netinet/in.h>

// A single connection.
struct host {
  char *name;
  int sockfd;
  struct sockaddr_in conn;
  int h_port;
  int c_port;
};

void init_hosts(char *file);

#endif
