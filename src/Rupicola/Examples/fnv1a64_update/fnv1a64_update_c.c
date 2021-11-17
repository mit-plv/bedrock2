#include <stdint.h>
uintptr_t update(uintptr_t hash, uintptr_t data) {
  return (hash^data)*1099511628211ULL;
}
