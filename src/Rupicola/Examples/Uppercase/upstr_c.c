#include <stdint.h>

void upstr(uintptr_t as, uintptr_t len) {
  char *s = (char*) as; int l = len;
  for (int pos = 0; pos < l; pos++) {
    s[pos] = (((unsigned)s[pos] - 'a') & 0xff) < 26 ? s[pos] & 0x5f : s[pos];
  }
}
