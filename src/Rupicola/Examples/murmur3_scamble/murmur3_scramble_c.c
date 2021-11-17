#include <stdint.h>
uintptr_t scramble(uintptr_t k) {
  k = k * 2331810129;
  k = (k << 15) | (k >> 17);
  k = k * 461845907;
  return k;
}
