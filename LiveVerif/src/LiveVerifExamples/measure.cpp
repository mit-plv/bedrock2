#include <iostream>
#include <chrono>
#include "onesize_malloc_globals.h"
#include "onesize_malloc_exported.h"
#include "critbit_exported.h"
#include <map>
#include <unordered_map>

// set exactly one to true
constexpr bool run_critbit = true;
constexpr bool run_stdmap = false;
constexpr bool run_stdunordmap = false;

// set at most one to true
constexpr bool do_delete = false;
constexpr bool do_lookup = true;
constexpr bool do_iter = false;

constexpr size_t n = 1 << 20;

uintptr_t hash(uintptr_t a, uintptr_t b) {
   return 37 * a + (a >> 23) + b;
}

int main(void) {
  std::cout << "critbit? " << (run_critbit ? "YES" : "NO") << std::endl;
  std::cout << "stdlib map? " << (run_stdmap ? "YES" : "NO") << std::endl;
  std::cout << "stdlib unordered_map? "
            << (run_stdunordmap ? "YES" : "NO") << std::endl;
  std::cout << "delete " << (do_delete ? "YES" : "NO") << std::endl;
  std::cout << "lookup " << (do_lookup ? "YES" : "NO") << std::endl;
  std::cout << "iter " << (do_iter ? "YES" : "NO") << std::endl;
  
  std::chrono::steady_clock::time_point begin;
  begin = std::chrono::steady_clock::now();

  // CRITBIT
  if constexpr (run_critbit) {
    // init memory
    const size_t chunk_size = n * 32 * 2;
    uintptr_t chunk = (uintptr_t)malloc(chunk_size);
    Malloc_init(chunk, chunk_size);

    // INSERT
    uintptr_t tp = cbt_init();
    uintptr_t nxt = 0;
    for (int i = 0; i < n; i++) {
      tp = cbt_insert(tp, nxt & ((1 << 20) - 1), 7 * i);
      nxt = hash(nxt, i);
    }

    // DELETE
    if constexpr (do_delete) {
      begin = std::chrono::steady_clock::now();
      nxt = 343;
      int hits = 0;
      for (int i = 0; i < n; i++) {
        hits += cbt_delete((uintptr_t)&tp, nxt & ((1 << 20) - 1));
        nxt = hash(nxt, i);
      }
      std::cout << hits << std::endl;
    }

    // LOOKUP
    if constexpr (do_lookup) {
      begin = std::chrono::steady_clock::now();
      nxt = 343;
      int hits = 0;
      uintptr_t dat;
      for (int i = 0; i < n; i++) {
        hits += cbt_lookup(tp, nxt & ((1 << 20) - 1), (uintptr_t)&dat);
        nxt = hash(nxt, i);
      }
      std::cout << hits << std::endl;
    }

    // ITER
    if constexpr (do_iter) {
      begin = std::chrono::steady_clock::now();
      uintptr_t ents = 0;
      uintptr_t sm = 0;
      uintptr_t last = 0;
      uintptr_t ko, vo;
      while (cbt_next_gt(tp, last, (uintptr_t)&ko, (uintptr_t)&vo)) {
        sm += vo;
        ents++;
        last = ko;
      }
      std::cout << ents << std::endl;
      std::cout << sm << std::endl;
    }
  }

  // STANDARD LIBRARY MAP
  if constexpr (run_stdmap) {
    // INSERTING
    std::map<uintptr_t, uintptr_t> mp;
    uintptr_t nxt = 0;
    for (int i = 0; i < n; i++) {
      mp[nxt & ((1 << 20) - 1)] = 7 * i;
      nxt = hash(nxt, i);
    }

    // DELETE
    if constexpr (do_delete) {
      begin = std::chrono::steady_clock::now();
      nxt = 343;
      int hits = 0;
      for (int i = 0; i < n; i++) {
        hits += mp.erase(nxt & ((1 << 20) - 1));
        nxt = hash(nxt, i);
      }
      std::cout << hits << std::endl;
    }

    // LOOKUP
    if constexpr (do_lookup) {
      begin = std::chrono::steady_clock::now();
      nxt = 343;
      int hits = 0;
      uintptr_t dat;
      for (int i = 0; i < n; i++) {
        hits += mp.find(nxt & ((1 << 20) - 1)) != mp.end();
        nxt = hash(nxt, i);
      }
      std::cout << hits << std::endl;
    }

    // ITER
    if constexpr (do_iter) {
      begin = std::chrono::steady_clock::now();
      uintptr_t ents = 0;
      uintptr_t sm = 0;
      auto it = mp.upper_bound(0);
      while (it != mp.end()) {
        sm += it->second;
        ents++;
        it++;
      }
      std::cout << ents << std::endl;
      std::cout << sm << std::endl;
    }
  }

  // STANDARD LIBRARY UNORDERED_MAP
  if constexpr (run_stdunordmap) {
    // INSERTING
    std::unordered_map<uintptr_t, uintptr_t> mp;
    uintptr_t nxt = 0;
    for (int i = 0; i < n; i++) {
      mp[nxt & ((1 << 20) - 1)] = 7 * i;
      nxt = hash(nxt, i);
    }

    // DELETE
    if constexpr (do_delete) {
      begin = std::chrono::steady_clock::now();
      nxt = 343;
      int hits = 0;
      for (int i = 0; i < n; i++) {
        hits += mp.erase(nxt & ((1 << 20) - 1));
        nxt = hash(nxt, i);
      }
      std::cout << hits << std::endl;
    }

    // LOOKUP
    if constexpr (do_lookup) {
      begin = std::chrono::steady_clock::now();
      nxt = 343;
      int hits = 0;
      uintptr_t dat;
      for (int i = 0; i < n; i++) {
        hits += mp.find(nxt & ((1 << 20) - 1)) != mp.end();
        nxt = hash(nxt, i);
      }
      std::cout << hits << std::endl;
    }

    // ITER
    if constexpr (do_iter) {
      std::cout << "No iteration for unordered_map! Exiting." << std::endl;
      exit(-1);
    }
  }

  std::chrono::steady_clock::time_point end = std::chrono::steady_clock::now();

  std::cout << "time = " << std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count() << "[µs]" << std::endl;
}
