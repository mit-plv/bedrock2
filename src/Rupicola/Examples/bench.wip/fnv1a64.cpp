#include <stdint.h>
#include <memory.h>

#define BENCH true

#if BENCH
#include <benchmark/benchmark.h>
#include <iostream>
#include <fstream>
#endif

#include "data.h"

// LITTLE-ENDIAN memory access is REQUIRED
// the following two functions are required to work around -fstrict-aliasing
static inline uintptr_t _br2_load(uintptr_t a, size_t sz) {
  uintptr_t r = 0;
  memcpy(&r, (void*)a, sz);
  return r;
}

static inline void _br2_store(uintptr_t a, uintptr_t v, size_t sz) {
  memcpy((void*)a, &v, sz);
}

uintptr_t bghash = (uintptr_t)14695981039346656037ULL;

uintptr_t __attribute__((noinline)) fnv1a(uintptr_t data, uintptr_t len) {
  uintptr_t step, hash, p, b, from;
  p = (uintptr_t)1099511628211ULL;
  hash = bghash;
  from = (uintptr_t)0ULL;
  step = (uintptr_t)1ULL;
  while ((from)<(len)) {
    b = _br2_load((data)+(((uintptr_t)1ULL)*(from)), 1);
    // b = *(char*)((data)+(((uintptr_t)1ULL)*(from)));
    hash = ((hash)^(b))*(p);
    // unset b
    from = (from)+((uintptr_t)1ULL);
  }

  return bghash = hash;
}

int64_t ghash = 14695981039346656037ULL;

int64_t __attribute__((noinline)) fnv1a_c_unsafe(char* data, int len) {
  int64_t p = 1099511628211ULL;
  int64_t hash = ghash;

  for (int pos = 0; pos < len; pos++) {
    hash = (hash ^ data[pos]) * p;
  }

  return ghash = hash;
}


#if BENCH

// dd if=/dev/urandom of=random.data bs=1MB count=10

static void BM_bedrock(benchmark::State& state) {
  const std::string fpath = "data.random";
  std::ifstream infile(fpath, std::ios_base::binary);

  std::vector<char> buffer{std::istreambuf_iterator<char>(infile),
    std::istreambuf_iterator<char>()};

  for (auto _ : state) {
    benchmark::DoNotOptimize(buffer.data());
    benchmark::ClobberMemory();
    benchmark::DoNotOptimize(fnv1a((uintptr_t)buffer.data(), buffer.size()));
    benchmark::ClobberMemory();
  }

  std::cout << ghash;
}

static void BM_C_unsafe(benchmark::State& state) {
  const std::string fpath = "data.random";
  std::ifstream infile(fpath, std::ios_base::binary);

  std::vector<char> buffer{std::istreambuf_iterator<char>(infile),
    std::istreambuf_iterator<char>()};

  for (auto _ : state) {
    benchmark::DoNotOptimize(buffer.data());
    benchmark::ClobberMemory();
    benchmark::DoNotOptimize(fnv1a_c_unsafe(buffer.data(), buffer.size()));
    benchmark::ClobberMemory();
  }

  std::cout << bghash;
}

BENCHMARK(BM_bedrock);
BENCHMARK(BM_C_unsafe);
BENCHMARK_MAIN();
#endif
