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

static uintptr_t utf8_decode(uintptr_t data, uintptr_t len, uintptr_t* c, uintptr_t* e);

void dummy_main(void) {
  /*skip*/
  return;
}

static uintptr_t utf8_decode(uintptr_t data, uintptr_t len, uintptr_t* _c, uintptr_t* _e) {
  uintptr_t offset, b0, mask, shiftc, min, c, b1, b2, b3, e, shifte;
  b0 = _br2_load((data)+(((uintptr_t)1ULL)*((uintptr_t)0ULL)), 1);
  len = ({ static const uint8_t _inlinetable[(uintptr_t)32ULL] = {1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 3, 3, 4, 0}; _br2_load((uintptr_t)&_inlinetable[(b0)>>((uintptr_t)3ULL)], 1); });
  offset = (len)+((len)==((uintptr_t)0ULL));
  b1 = _br2_load((data)+(((uintptr_t)1ULL)*((uintptr_t)1ULL)), 1);
  b2 = _br2_load((data)+(((uintptr_t)1ULL)*((uintptr_t)2ULL)), 1);
  b3 = _br2_load((data)+(((uintptr_t)1ULL)*((uintptr_t)3ULL)), 1);
  mask = ({ static const uint8_t _inlinetable[(uintptr_t)5ULL] = {0, 127, 31, 15, 7}; _br2_load((uintptr_t)&_inlinetable[len], 1); });
  c = ((b0)&(mask))<<((uintptr_t)18ULL);
  c = (c)|(((b1)&((uintptr_t)63ULL))<<((uintptr_t)12ULL));
  c = (c)|(((b2)&((uintptr_t)63ULL))<<((uintptr_t)6ULL));
  c = (c)|(((b3)&((uintptr_t)63ULL))<<((uintptr_t)0ULL));
  shiftc = ({ static const uint8_t _inlinetable[(uintptr_t)5ULL] = {0, 18, 12, 6, 0}; _br2_load((uintptr_t)&_inlinetable[len], 1); });
  c = (c)>>(shiftc);
  min = ({ static const uint8_t _inlinetable[(uintptr_t)5ULL] = {0, 0, 128, 0, 0}; _br2_load((uintptr_t)&_inlinetable[len], 1); });
  e = ((c)<(min))<<((uintptr_t)6ULL);
  e = (e)|((((c)>>((uintptr_t)11ULL))==((uintptr_t)27ULL))<<((uintptr_t)7ULL));
  e = (e)|((((uintptr_t)1114111ULL)<(c))<<((uintptr_t)8ULL));
  e = (e)|(((b1)&((uintptr_t)192ULL))>>((uintptr_t)2ULL));
  e = (e)|(((b2)&((uintptr_t)192ULL))>>((uintptr_t)4ULL));
  e = (e)|((b3)>>((uintptr_t)6ULL));
  e = (e)^((uintptr_t)42ULL);
  shifte = ({ static const uint8_t _inlinetable[(uintptr_t)5ULL] = {0, 6, 4, 2, 0}; _br2_load((uintptr_t)&_inlinetable[len], 1); });
  e = (e)>>(shifte);
  *_c = c;
  *_e = e;
  return offset;
}

