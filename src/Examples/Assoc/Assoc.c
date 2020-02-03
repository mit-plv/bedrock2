#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <stdint.h>
#include <stdbool.h>

typedef uint32_t key;
typedef char* value;

typedef struct {
  key k;
  value v;
} kv;

bool assoc_cpy(kv pairs[], size_t len, key k, kv** out) {
  kv* end = pairs + len;
  while (pairs < end) {
    if (pairs->k == k) {
      *out = pairs;
      return true;
    }
    ++pairs;
  }
  return false;
}

kv* assoc_ptr(kv pairs[], size_t len, key k) {
  kv* end = pairs + len;
  while (pairs < end) {
    if (pairs->k == k) {
      return pairs;
    }
    ++pairs;
  }
  return NULL;
}

// Tests

#define DATA_LEN 5
#define KEYS_LEN 12

int main() {
  kv data[DATA_LEN] = {{.k = 0xa92ed050, .v = "apple"},
                       {.k = 0x1dc5b178, .v = "orange"},
                       {.k = 0xc68a3cbd, .v = "pear"},
                       {.k = 0x791e24d3, .v = "blueberry"},
                       {.k = 0xde75697c, .v = "kiwi"}};

  key keys[KEYS_LEN] =
    {0xa92ed050, 0x1dc5b178, 0xc68a3cbd, 0x791e24d3, 0xde75697c, 0x89ac3b1d,
     0xdf03c020, 0x6ee08f0d, 0x763afb5f, 0xa16969e3, 0xa3136f1f, 0x95be4b1f};

  size_t kid = 0;
  for (kid = 0; kid < KEYS_LEN; kid++) {
    key k = keys[kid];

    kv* out;
    if (assoc_cpy(data, DATA_LEN, k, &out)) {
      printf("[cpy] %x: {%x, %s}\n", k, out->k, out->v);
    } else {
      printf("[cpy] %x: not found\n", k);
    }

    kv* out_ptr = assoc_ptr(data, DATA_LEN, k);
    if (out_ptr) {
      printf("[ptr] %x: {%x, %s}\n", k, out->k, out->v);
    } else {
      printf("[ptr] %x: not found\n", k);
    }
  }

  return 0;
}
