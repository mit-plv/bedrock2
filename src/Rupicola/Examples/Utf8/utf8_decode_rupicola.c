#include "utf8_decode1_rupicola.h"
#include <stddef.h>

uintptr_t utf8_decode_all(uint8_t* p, size_t len) {
	uintptr_t ret = 0;
	uint8_t* end = p + len - 4;
	while (p < end) {
		uintptr_t c, e;
		p = (uint8_t*)utf8_decode((uintptr_t)p, &c, &e);
		ret += !!e;
	}
	return ret;
}
