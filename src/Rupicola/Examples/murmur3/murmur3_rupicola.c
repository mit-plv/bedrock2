#include <stdint.h>
#include <stddef.h>
#include <memory.h>
#include "murmur3_scramble_rupicola.h"

uint32_t murmur3_32(const uint8_t *key, uintptr_t len) {
  uint32_t h = 0;
  uint32_t k;
  /* Read in groups of 4. */
  for (size_t i = len >> 2; i; i--) {
    // Here is a source of differing results across endiannesses.
    // A swap here has no effects on hash properties though.
    memcpy(&k, key, sizeof(uint32_t));
    key += sizeof(uint32_t);
    h ^= scramble(k);
    h = (h << 13) | (h >> 19);
    h = h * 5 + 0xe6546b64;
  }
  /* Read the rest. */
  k = 0;
  for (size_t i = len & 3; i; i--) {
    k <<= 8;
    k |= key[i - 1];
  }
  // A swap is *not* necessary here because the preceding loop already
  // places the low bytes in the low places according to whatever endianness
  // we use. Swaps only apply when the memory is copied in a chunk.
  h ^= scramble(k);
  /* Finalize. */
  h ^= len;
  h ^= h >> 16;
  h *= 0x85ebca6b;
  h ^= h >> 13;
  h *= 0xc2b2ae35;
  h ^= h >> 16;
  return h;
}
