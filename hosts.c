#include "hosts.h"
#include <arpa/inet.h>
#include <netinet/in.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>

struct host *conns[1024];
int num_conns = 0;
char *glob_name;

int init_conn(int h_port) {

  int sock_fd = socket(AF_INET, SOCK_DGRAM, 0);

  if (sock_fd < 0) {
    printf("Socket initialization failed.");
    exit(1);
  }

  struct sockaddr_in serv_addr;

  memset(&serv_addr, 0, sizeof(serv_addr));

  serv_addr.sin_family = AF_INET;
  serv_addr.sin_port = htons(h_port);
  serv_addr.sin_addr.s_addr = htonl(INADDR_ANY);

  if (bind(sock_fd, (struct sockaddr *)&serv_addr, sizeof(serv_addr)) < 0) {
    printf("Failed to bind socket.\n");
    exit(1);
  }

  return sock_fd;
}

void init_hosts(char *file) {

  char *line = NULL;
  size_t len = 0;
  ssize_t read;

  FILE *fp = fopen(file, "r");
  if (fp == NULL) {
    printf("Host file not found.\n");
    exit(1);
  }

  int name = 1;

  while ((read = getline(&line, &len, fp)) != -1) {
    if (name == 1) {
      glob_name = malloc(sizeof(char) * (strlen(line) + 1));
      strcpy(glob_name, line);
      glob_name[strcspn(glob_name, "\n")] = 0;
      printf("Name: %s", glob_name);
      name = 0;
    } else {
      char *cname = malloc(200 * sizeof(char));
      char *addr = malloc(32 * sizeof(char));
      int c_port;
      int h_port;
      int ret = sscanf(line, "%200s %d %32s %d", cname, &h_port, addr, &c_port);
      if (ret != 4) {
        printf("Could not parse host file.\n");
        exit(1);
      }
      struct host *h = malloc(sizeof(struct host));
      h->name = cname;
      h->h_port = h_port;
      h->c_port = c_port;
      h->sockfd = init_conn(h_port);

      struct sockaddr_in conn_addr;

      memset(&conn_addr, 0, sizeof(conn_addr));

      conn_addr.sin_family = AF_INET;
      conn_addr.sin_port = htons(c_port);
      conn_addr.sin_addr.s_addr = inet_addr(addr);
      free(addr);
      h->conn = conn_addr;
      conns[num_conns] = h;
      num_conns += 1;
    }
  }
}
