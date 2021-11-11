#include <stdint.h>
#include <memory.h>

#if defined(BENCH) || defined(MAIN)
#include <iostream>
#include <fstream>
#include <vector>
#endif

#if defined(BENCH)
#include <benchmark/benchmark.h>
#endif

#include "data.h"
// LITTLE-ENDIAN memory access is REQUIRED
// the following two functions are required to work around -fstrict-aliasing
static
__attribute__((noinline))
uintptr_t _br2_load(uintptr_t a, size_t sz) {
  uintptr_t r = 0;
  memcpy(&r, (void*)a, sz);
  return r;
}

static
__attribute__((noinline))
uintptr_t _br2_load_masked(uintptr_t a, size_t sz) {
  uintptr_t r = 0;
  memcpy(&r, (void*)a, sizeof(uintptr_t));
  uintptr_t mask = sz == sizeof(uintptr_t) ? (uintptr_t)-1 : (1 << 8 * sz) - 1;
  // uintptr_t mask = ~(((uintptr_t)-1) >> 8 * sz << 8 * sz);
  return r & mask;
}

#define READ8(S) ((255 & (S)[0]))
#define READ16LE(S) ((255 & (S)[1]) << 8 | (255 & (S)[0]))
#define READ32LE(S)                                                    \
  ((uint32_t)(255 & (S)[3]) << 030 | (uint32_t)(255 & (S)[2]) << 020 | \
   (uint32_t)(255 & (S)[1]) << 010 | (uint32_t)(255 & (S)[0]) << 000)

static
__attribute__((noinline))
uintptr_t _br2_load_branched(uintptr_t a, size_t sz) {
  if (sz == 1)
    return READ8((unsigned char*)a);
  if (sz == 2)
    return READ16LE((unsigned char*)a);
  if (sz == 4)
    return READ32LE((unsigned char*)a);
  __builtin_unreachable();
}

uintptr_t
__attribute__((noinline))
fnv1a (uintptr_t data, uintptr_t len, uintptr_t hash) {
  uintptr_t step, p, b, from;

  p = (uintptr_t)1099511628211ULL;
  from = (uintptr_t)0ULL;
  step = (uintptr_t)1ULL;

  while ((from)<(len)) {
    b = _br2_load((data)+(((uintptr_t)1ULL)*(from)), 1);
    hash = ((hash)^(b))*(p);
    from = (from)+((uintptr_t)1ULL);
  }

  return hash;
}

uintptr_t
__attribute__((noinline))
fnv1a_masked (uintptr_t data, uintptr_t len, uintptr_t hash) {
  uintptr_t step, p, b, from;

  p = (uintptr_t)1099511628211ULL;
  from = (uintptr_t)0ULL;
  step = (uintptr_t)1ULL;

  while ((from)<(len)) {
    b = _br2_load_masked((data)+(((uintptr_t)1ULL)*(from)), 1);
    hash = ((hash)^(b))*(p);
    from = (from)+((uintptr_t)1ULL);
  }

  return hash;
}

uintptr_t
__attribute__((noinline))
fnv1a_branched (uintptr_t data, uintptr_t len, uintptr_t hash) {
  uintptr_t step, p, b, from;

  p = (uintptr_t)1099511628211ULL;
  from = (uintptr_t)0ULL;
  step = (uintptr_t)1ULL;

  while ((from)<(len)) {
    b = _br2_load_branched((data)+(((uintptr_t)1ULL)*(from)), 1);
    hash = ((hash)^(b))*(p);
    from = (from)+((uintptr_t)1ULL);
  }

  return hash;
}

#define REPEATS 1000000000ULL

uintptr_t start = (uintptr_t)14695981039346656037ULL;
uintptr_t p0 = (uintptr_t)(1099511628211ULL >> 1);

volatile uintptr_t data;
volatile uintptr_t len;

uintptr_t __attribute__((noinline))
repeat() {
  uintptr_t ghash = start;
  for (unsigned long long i = 0; i < REPEATS; i++) {
    ghash = fnv1a(data, len, ghash) * p0;
  }
  return ghash;
}

uintptr_t __attribute__((noinline))
repeat_masked() {
  uintptr_t ghash = start;
  for (unsigned long long i = 0; i < REPEATS; i++) {
    ghash = fnv1a_masked(data, len, ghash) * p0;
  }
  return ghash;
}

uintptr_t __attribute__((noinline))
repeat_branched() {
  uintptr_t ghash = start;
  for (unsigned long long i = 0; i < REPEATS; i++) {
    ghash = fnv1a_branched(data, len, ghash) * p0;
  }
  return ghash;
}

#ifdef MAIN

int main(int argc, char** argv) {
  const std::string fpath = "data.random";
  std::ifstream infile(fpath, std::ios_base::binary);

  std::vector<char> buffer{std::istreambuf_iterator<char>(infile),
    std::istreambuf_iterator<char>()};

  data = (uintptr_t)buffer.data();
  len = buffer.size();

  std::string mode = argc > 1 ? std::string(argv[1]) : "memcpy";
  uintptr_t ghash = 0;
  if (mode == "memcpy") {
    ghash = repeat();
  } else if (mode == "masked") {
    ghash = repeat_masked();
  } else if (mode == "branched") {
    ghash = repeat_branched();
  }

  std::cout << "hash: " << ghash << std::endl;
}

#endif

#ifdef BENCH

// dd if=/dev/urandom of=random.data bs=1MB count=10

uintptr_t ghash = 0;

static void BM_old(benchmark::State& state) {
  const std::string fpath = "data.random";
  std::ifstream infile(fpath, std::ios_base::binary);

  std::vector<char> buffer{std::istreambuf_iterator<char>(infile),
    std::istreambuf_iterator<char>()};

  for (auto _ : state) {
    benchmark::DoNotOptimize(buffer.data());
    benchmark::ClobberMemory();
    benchmark::DoNotOptimize(ghash = fnv1a((uintptr_t)buffer.data(), buffer.size()));
    benchmark::ClobberMemory();
  }

  std::cout << ghash;
}

static void BM_new(benchmark::State& state) {
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

BENCHMARK(BM_bedrock);
BENCHMARK(BM_C_unsafe);
BENCHMARK_MAIN();
#endif
