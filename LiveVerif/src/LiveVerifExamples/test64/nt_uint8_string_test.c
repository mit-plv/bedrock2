#include <stdio.h>
#include "nt_uint8_string_exported.h"
#include "../testing.h"

const char* s1 = "Hello World";
const char* s2 = "Hello, World";
const char* s3 = "Hello";
const char* s4 = "Hello World";
const char* s5 = "";
const char* s6 = "";

intptr_t sign(uintptr_t v) {
  if (v == 0) return 0;
  if (((intptr_t)v) < 0) return -1;
  return 1;
}

void test_Strcmp(intptr_t expected, const char* s1, const char* s2) {
  assert_equal_signed(expected, sign(Strcmp((uintptr_t)s1, (uintptr_t)s2)));
}

#define LT -1
#define EQ 0
#define GT 1

int main() {
  test_Strcmp(LT, s1, s2);
  test_Strcmp(GT, s1, s3);
  test_Strcmp(EQ, s1, s4);
  test_Strcmp(GT, s1, s5);
  test_Strcmp(GT, s2, s1);
  test_Strcmp(LT, s3, s1);
  test_Strcmp(EQ, s4, s1);
  test_Strcmp(LT, s5, s1);
  test_Strcmp(EQ, s5, s6);
  printf("OK\n");
}
