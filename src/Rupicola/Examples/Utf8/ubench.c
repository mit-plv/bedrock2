#include <x86intrin.h>
#include <stdio.h>

#define WARMUP 50
#define TRIALS (100  /*odd for median*/|1)
#define COOLDOWN 50
#define LAPS (WARMUP+TRIALS+COOLDOWN)

#include "testdata.c"
void utf8_decode_all(uint8_t* buf, size_t len);

int compare_uint64_t(const void* pa, const void* pb) {
	uint64_t a = *(uint64_t*)pa;
	uint64_t b = *(uint64_t*)pb;
	if (a < b) { return -1; }
	if (a > b) { return  1; }
	return 0;
}

int main() {
	uint8_t buf[1024*1024];
	buffer_fill(&buf, sizeof(buf));

	uint64_t laptimes[LAPS+1];
	for (int i=0; i<LAPS; i++) {
		laptimes[i] = __rdtsc();
		{
			utf8_decode_all(buf, sizeof(buf));
		}
	}
	laptimes[LAPS] = __rdtsc();
	uint64_t total = laptimes[WARMUP+TRIALS] - laptimes[WARMUP];
	for (int i=0; i<LAPS; i++) {
		laptimes[i] = laptimes[i+1] - laptimes[i];
	}
	qsort(&laptimes[WARMUP], TRIALS, sizeof(laptimes[0]), compare_uint64_t);
	uint64_t min = laptimes[WARMUP];
	uint64_t max = laptimes[WARMUP+TRIALS-1];
	uint64_t median = laptimes[WARMUP+TRIALS/2];
	printf ("n=%d; min=%llu; median=%llu; max=%llu; mean=%llu/%d;\n", TRIALS, min, median, total, max, TRIALS);
}
