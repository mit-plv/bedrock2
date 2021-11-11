#include <stdint.h>
#include <memory.h>

// LITTLE-ENDIAN memory access is REQUIRED
// the following two functions are required to work around -fstrict-aliasing
static inline uintptr_t _br2_load(uintptr_t a, size_t sz) {
  uintptr_t r = 0;
  memcpy(&r, (void*)a, sz);
  return r;
}

static inline void _br2_store(uintptr_t a, uintptr_t v, size_t sz) {
  memcpy((void*)a, &v, sz);
}


uintptr_t fnv1a(uintptr_t data, uintptr_t len) {
  uintptr_t step, hash, p, b, from;
  p = (uintptr_t)FIXME;
  hash = (uintptr_t)FIXME;
  from = (uintptr_t)0ULL;
  step = (uintptr_t)1ULL;
  while ((from)<(len)) {
    b = _br2_load((data)+(((uintptr_t)1ULL)*(from)), 1);
    hash = ((hash)^(b))*(p);
    // unset b
    from = (from)+((uintptr_t)1ULL);
  }
  return hash;
}
