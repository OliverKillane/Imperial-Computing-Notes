#include <benchmark/benchmark.h>

// In order to benchmark function calls, we first benchmark nothing...
void nothing_fun() {}
auto nothing_lda = []() {};
void (*nothing_ptr)(void) = +[]() {};
std::function<void(void)> nothing_std = []() {};

#define NOTHING_BENCH(FN)                                                      \
  static void benchmark_##FN(benchmark::State &state) {                        \
    for (auto _ : state) {                                                     \
      for (size_t i = 0; i < state.range(0); i++) {                            \
        FN();                                                                  \
      }                                                                        \
    }                                                                          \
  }                                                                            \
  BENCHMARK(benchmark_##FN)->Range(8 * 1024, 64 * 1024);

NOTHING_BENCH(nothing_fun)
NOTHING_BENCH(nothing_lda)
NOTHING_BENCH(nothing_ptr)
NOTHING_BENCH(nothing_std)

BENCHMARK_MAIN();
