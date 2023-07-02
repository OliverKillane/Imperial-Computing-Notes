#include "sorts/heapsort.h"
#include "sorts/quicksort.h"
#include "sorts/mergesort.h"

#include "generate.h"

#include <benchmark/benchmark.h>

template<void sort(vector<int>&), vector<int> generate(size_t)>
static void sort_ints(benchmark::State &state) {
  for (auto _ : state) {
    state.PauseTiming();
    vector<int> workload(generate(state.range(0))); 
    state.ResumeTiming();
    sort(workload);
    // benchmark::DoNotOptimize(workload);
  }
}

constexpr auto intcomp = [](const int& a, const int& b) -> bool {return a > b;};

#define BENCH_SORT(SORT, GEN) BENCHMARK(sort_ints<SORT<int, +intcomp>, GEN>)->Range(8 * 1024, 64 * 1024);
 
BENCH_SORT(heapsort, random_ints);
BENCH_SORT(quicksort, random_ints);
BENCH_SORT(mergesort, random_ints);

BENCH_SORT(heapsort, alternating_ints);
BENCH_SORT(quicksort, alternating_ints);
BENCH_SORT(mergesort, alternating_ints);

BENCH_SORT(heapsort, ordered_ints);
BENCH_SORT(quicksort, ordered_ints);
BENCH_SORT(mergesort, ordered_ints);

BENCH_SORT(heapsort, reverse_ordered_ints);
BENCH_SORT(quicksort, reverse_ordered_ints);
BENCH_SORT(mergesort, reverse_ordered_ints);

BENCHMARK_MAIN();
