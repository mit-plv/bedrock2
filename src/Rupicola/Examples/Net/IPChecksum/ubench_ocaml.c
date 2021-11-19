#include <x86intrin.h>
#include <stdio.h>
#include <inttypes.h>

#define WARMUP 10
#define TRIALS (100  /* >100 for normal distribution approximation, odd for median*/|1)
#define COOLDOWN 1
#define LAPS (WARMUP+TRIALS+COOLDOWN)

#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/callback.h>

#include "testdata.c"

int main(int argc, char **argv) {
  uint8_t buf[1024 * 1024];
  buffer_fill(buf, sizeof(buf));

  caml_startup(argv);

  CAMLparam0();
  CAMLlocal2(ocaml_buf, ocaml_list);
  ocaml_buf = caml_alloc_initialized_string(sizeof(buf), buf);
  ocaml_list = caml_callback(*caml_named_value("list_char_of_string"), ocaml_buf);
  const value ocaml_ip_checksum = *caml_named_value("ip_checksum");

  uint64_t laptimes[LAPS + 1];
  for (int i = 0; i < LAPS; i++) {
    laptimes[i] = __rdtsc();
    {
	    caml_callback(ocaml_ip_checksum, ocaml_list);
    }
  }
  laptimes[LAPS] = __rdtsc();
  for (int i = 0; i < LAPS; i++) {
    laptimes[i] = laptimes[i + 1] - laptimes[i];
  }

  printf("[%" PRIu64, laptimes[WARMUP]);
  for (int i = WARMUP + 1; i < WARMUP + TRIALS; i++) {
    printf(", %" PRIu64, laptimes[i]);
  }
  printf("]");
}
