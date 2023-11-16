#include <stdint.h>

// will be initialized by malloc_init
uintptr_t malloc_state;
const uintptr_t malloc_state_ptr = (uintptr_t)(&malloc_state);

// adapt depending on application
const uintptr_t malloc_block_size = 16;
