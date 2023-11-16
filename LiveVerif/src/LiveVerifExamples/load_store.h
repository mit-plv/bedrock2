#ifndef LOAD_STORE_H
#define LOAD_STORE_H

// We use memcpy to work around -fstrict-aliasing.
// See bedrock2.ToCString for further notes.

static inline  __attribute__((always_inline, unused))
uintptr_t load8(uintptr_t a) {
  uint8_t r = 0;
  memcpy(&r, (void*)a, 1);
  return r;
}

static inline  __attribute__((always_inline, unused))
uintptr_t load16(uintptr_t a) {
  uint16_t r = 0;
  memcpy(&r, (void*)a, 2);
  return r;
}

static inline  __attribute__((always_inline, unused))
uintptr_t load32(uintptr_t a) {
  uint32_t r = 0;
  memcpy(&r, (void*)a, 4);
  return r;
}

static inline  __attribute__((always_inline, unused))
uintptr_t load(uintptr_t a) {
  uintptr_t r = 0;
  memcpy(&r, (void*)a, sizeof(r));
  return r;
}

// same runtime behavior, but changes proof automation
#define deref8 load8
#define deref16 load16
#define deref32 load32
#define deref load

static inline __attribute__((always_inline, unused))
void store8(uintptr_t a, uintptr_t v) {
  memcpy((void*)a, &v, 1);
}

static inline __attribute__((always_inline, unused))
void store16(uintptr_t a, uintptr_t v) {
  memcpy((void*)a, &v, 2);
}

static inline __attribute__((always_inline, unused))
void store32(uintptr_t a, uintptr_t v) {
  memcpy((void*)a, &v, 4);
}

static inline __attribute__((always_inline, unused))
void store(uintptr_t a, uintptr_t v) {
  memcpy((void*)a, &v, sizeof(v));
}

#endif /* LOAD_STORE_H */
