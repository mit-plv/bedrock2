#include <stdint.h>

// We use bytewise access to work around -fstrict-aliasing.
// On clang 10, these functions could be replaced with memcpy but gcc 11
// seems to fail to infer the bounds on an integer loaded by memcpy.
// Adding a range mask after memcpy in turn makes slower code in clang.
// The little-endian memory access idioms below are fast in both.
static inline uintptr_t _br2_load(uintptr_t a, uintptr_t sz) {
  uint8_t* p = (uint8_t*) a;
  uintptr_t r = 0;
  switch (sz) {
    case 8: r |= (uintptr_t)p[7] << 56;
            r |= (uintptr_t)p[6] << 48;
            r |= (uintptr_t)p[5] << 40;
            r |= (uintptr_t)p[4] << 32;
            // fall through
    case 4: r |= (uintptr_t)p[3] << 24;
            r |= (uintptr_t)p[2] << 16;
            // fall through
    case 2: r |= (uintptr_t)p[1] << 8;
            // fall through
    case 1: r |= (uintptr_t)p[0];
  }
  return r;
}

static inline void _br2_store(uintptr_t a, uintptr_t v, uintptr_t sz) {
  uint8_t* p = (uint8_t*) a;
  switch (sz) {
    case 8: p[7] = v >> 56;
            p[6] = v >> 48;
            p[5] = v >> 40;
            p[4] = v >> 32;
            // fall through
    case 4: p[3] = v >> 24;
            p[2] = v >> 16;
            // fall through
    case 2: p[1] = v >> 8;
            // fall through
    case 1: p[0] = v;
  }
}


uintptr_t scramble(uintptr_t k) {
  k = (k)*((uintptr_t)2331810129ULL);
  k = ((k)<<((uintptr_t)15ULL))|((k)>>((uintptr_t)17ULL));
  k = (k)*((uintptr_t)461845907ULL);
  return k;
}


