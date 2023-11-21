#include <stdio.h>
#include "min_exported.h"
#include "../testing.h"

int main() {
  assert_equal(3, u_min(3, 4));
  assert_equal(42, u_min(42, 4845));
  printf("OK\n");
  return 0;
}
