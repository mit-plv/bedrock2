#include <stdio.h>
#include "memset_exported.h"
#include "../testing.h"

int main() {
  char b[10];
  memset(b, 42, 10);
  for (int i = 0; i < 10; i++) {
    assert_equal(42, b[i]);
  }
  printf("OK\n");
  return 0;
}
