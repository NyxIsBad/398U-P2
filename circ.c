#include "circ.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX(x, y) (((x) > (y)) ? (x) : (y))

struct wires *g_wires;

void init_circuit(char *file) {

  char *line = NULL;
  size_t len = 0;
  ssize_t read;

  g_wires = NULL;

  FILE *fp = fopen(file, "r");
  if (fp == NULL) {
    printf("Circuit file not found.\n");
    exit(1);
  }

  while ((read = getline(&line, &len, fp)) != -1) {
    char *wname = malloc(200 * sizeof(char));
    char op[4];
    char *in1 = malloc(200 * sizeof(char));
    char *in2 = malloc(200 * sizeof(char));
    int ret = sscanf(line, "%200s = %3s %200s %200s", wname, op, in1, in2);
    if (ret == 4) {
      if (strcmp(op, "inp") == 0) {
        struct wire *w = malloc(sizeof(struct wire));
        w->wname = wname;
        w->operation = 2;
        w->val = from(atoi(in2));
        w->depth = 0;
        w->in1 = NULL;
        w->in2 = NULL;
        w->is_output = 0;
        w->input_name = in1;
        struct wires *cur = malloc(sizeof(struct wires));
        cur->w = w;
        cur->next = g_wires;
        g_wires = cur;
      } else if (strcmp(op, "add") == 0) {
        struct wire *inw1;
        struct wire *inw2;
        struct wires *a;
        for (a = g_wires; a != NULL; a = a->next) {
          if (strcmp(a->w->wname, in1) == 0) {
            inw1 = a->w;
          }
          if (strcmp(a->w->wname, in2) == 0) {
            inw2 = a->w;
          }
        }

        struct wire *w = malloc(sizeof(struct wire));
        w->wname = wname;
        w->operation = 0;
        w->val = 0;
        w->depth = MAX(inw1->depth, inw2->depth) + 1;
        w->in1 = inw1;
        w->in2 = inw2;
        w->is_output = 0;
        struct wires *cur = malloc(sizeof(struct wires));
        cur->w = w;
        cur->next = g_wires;
        g_wires = cur;

      } else if (strcmp(op, "mul") == 0) {
        struct wire *inw1;
        struct wire *inw2;
        struct wires *a;
        for (a = g_wires; a != NULL; a = a->next) {
          if (strcmp(a->w->wname, in1) == 0) {
            inw1 = a->w;
          }
          if (strcmp(a->w->wname, in2) == 0) {
            inw2 = a->w;
          }
        }
        struct wire *w = malloc(sizeof(struct wire));
        w->wname = wname;
        w->operation = 1;
        w->val = 0;
        w->depth = MAX(inw1->depth, inw2->depth) + 1;
        w->in1 = inw1;
        w->in2 = inw2;
        w->is_output = 0;
        struct wires *cur = malloc(sizeof(struct wires));
        cur->w = w;
        cur->next = g_wires;
        g_wires = cur;
      }
    } else if (ret == 3) {
      if (strcmp(op, "inp") == 0) {

        struct wire *w = malloc(sizeof(struct wire));
        w->wname = wname;
        w->operation = 2;
        w->val = 0;
        w->depth = 0;
        w->in1 = NULL;
        w->in2 = NULL;
        w->is_output = 0;
        w->input_name = in1;
        struct wires *cur = malloc(sizeof(struct wires));
        cur->w = w;
        cur->next = g_wires;
        g_wires = cur;
      } else if (strcmp(op, "con") == 0) {
        struct wire *w = malloc(sizeof(struct wire));
        w->wname = wname;
        w->operation = 3;
        w->val = from(atoi(in1));
        w->depth = 0;
        w->in1 = NULL;
        w->in2 = NULL;
        w->is_output = 0;
        struct wires *cur = malloc(sizeof(struct wires));
        cur->w = w;
        cur->next = g_wires;
        g_wires = cur;
      }
    } else {
      char *wwname = malloc(200 * sizeof(char));
      int nret = sscanf(line, "out %200s", wwname);
      if (nret == 1) {
        struct wire *inw1;
        struct wires *a;
        for (a = g_wires; a != NULL; a = a->next) {
          if (strcmp(a->w->wname, wwname) == 0) {
            inw1 = a->w;
          }
        }
        inw1->is_output = 1;
      }
      // otherwise ignore the command
    }
  }

  struct wires *cur = g_wires;
  struct wires *prev = NULL;
  struct wires *next;

  while (cur != NULL) {
    next = cur->next;
    cur->next = prev;
    prev = cur;
    cur = next;
  }

  g_wires = prev;
}
