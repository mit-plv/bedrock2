#include <stdio.h>
#include <stdlib.h>

void assert_equal(uintptr_t a, uintptr_t b) {
  if (a != b) {
    fprintf(stderr, "Assertion failure\n");
    exit(3);
  }
}
