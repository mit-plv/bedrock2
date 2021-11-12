#include <stdint.h>

void upstr(uintptr_t as, uintptr_t len) {
  char *s = (char*) as;
  for (int pos = 0; pos < len; pos++) {
    s[pos] = (unsigned)s[pos] - 'a' < 26 ? s[pos] & 0x5f : s[pos];
  }
}
