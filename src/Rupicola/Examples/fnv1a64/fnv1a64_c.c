#include <stdint.h>
uint64_t fnv1a(char* data, uintptr_t len) {
  static const uint64_t p = 1099511628211ULL;
  uint64_t hash = 14695981039346656037ULL;

  for (int pos = 0; pos < len; pos++) {
    hash = (hash ^ data[pos]) * p;
  }

  return hash;
}
