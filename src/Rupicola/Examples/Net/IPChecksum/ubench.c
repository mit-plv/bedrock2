#include <x86intrin.h>
#include <stdio.h>
#include <inttypes.h>

#define WARMUP 100
#define TRIALS (1000  /* >100 for normal distribution approximation, odd for median*/|1)
#define COOLDOWN 10
#define LAPS (WARMUP+TRIALS+COOLDOWN)

#include "testdata.c"
void ip_checksum(uintptr_t bufaddr, uintptr_t len);

int main(int argc, char** argv) {
	uint8_t buf[1024*1024];
	buffer_fill(buf, sizeof(buf));

	uint64_t laptimes[LAPS+1];
	for (int i=0; i<LAPS; i++) {
		laptimes[i] = __rdtsc();
		{
			ip_checksum((uintptr_t)buf, (uintptr_t)sizeof(buf));
		}
	}
	laptimes[LAPS] = __rdtsc();
	for (int i=0; i<LAPS; i++) {
		laptimes[i] = laptimes[i+1] - laptimes[i];
	}

	printf("[%" PRIu64, laptimes[WARMUP]);
	for (int i=WARMUP+1; i<WARMUP+TRIALS; i++) {
		printf(", %" PRIu64, laptimes[i]);
	}
	printf("]");
}
