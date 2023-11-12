#include <stdint.h>
#include <assert.h>
#include <stdio.h>

/*
Notes on how to implement Bedrock2's stackalloc in C:

uintptr_t a = stackalloc(N);
==>
uintptr_t a = ((uint8_t [N]) {0});
// using compound literals: https://gcc.gnu.org/onlinedocs/gcc/Compound-Literals.html

alternatives:

uintptr_t a = stackalloc(N);
==>
uintptr_t a = alloca(N);
// BAD because UB if code reads uninitialized data

stackalloc(a, N, {
  body
}) ==>
byte a[N] = {0}; { body }
// a little awkward syntax
// 0-initialization to avoid UB in case of read,
// modeled as readable anyvals in bedrock2
*/

#define stackalloc(N) ((uintptr_t)((uint8_t [N]) {0}))

static_assert(1 + 1 == 2, "this is a test");

int main() {
  uintptr_t x = stackalloc(16);
  *((uintptr_t*)x) = ((uintptr_t) 42);
  *((uintptr_t*)(x + 8)) = ((uintptr_t) 43);
  uintptr_t v1 = *((uintptr_t*) x);
  uintptr_t v2 = *((uintptr_t*) (x+8));
  printf("%d %d\n", v1, v2);
}
