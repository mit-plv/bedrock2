#include <stdint.h>
#include <x86intrin.h>
#include <stdio.h>
#include <math.h>

#define WARMUP 100
#define TRIALS (1000  /* >100 for normal distribution approximation, odd for median*/|1)
#define COOLDOWN 10
#define LAPS (WARMUP+TRIALS+COOLDOWN)

uintptr_t scramble(uintptr_t data);

int compare_uint64_t(const void* pa, const void* pb) {
	uint64_t a = *(uint64_t*)pa;
	uint64_t b = *(uint64_t*)pb;
	if (a < b) { return -1; }
	if (a > b) { return  1; }
	return 0;
}

int main() {
	uint64_t laptimes[LAPS+1];
	for (int i=0; i<LAPS; i++) {
		laptimes[i] = __rdtsc();
		{
			scramble(0);
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

	double mean = laptimes[WARMUP], squared_distance_from_mean = 0;
	for (int i=1; i<TRIALS; i++) {
	        double delta = laptimes[WARMUP+i] - mean;
	        mean += delta / (i+1);
	        double delta2 = laptimes[WARMUP+i] - mean;
		squared_distance_from_mean += delta * delta2;
	}
	double stddev = sqrt(squared_distance_from_mean/(TRIALS-1));
	double d95 = 1.95996398454005423552*stddev/sqrt(TRIALS), ci95lo = mean-d95, ci95hi = mean+d95;
	printf ("n=%d; min=%llu; median=%llu; max=%llu; mean=%.0f; stddev=%.0f; ci95lo=%.0f; ci95hi=%.0f;\n", TRIALS, min, median, max, mean, stddev, ci95lo, ci95hi);
}
