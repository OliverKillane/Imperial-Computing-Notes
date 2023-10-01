#include "partitions/in_place_conditional.h"
#include "partitions/in_place_predicated.h"
#include "partitions/out_of_place_conditional.h"
#include "partitions/out_of_place_predicated.h"

#include <benchmark/benchmark.h>

std::vector<int> ordered_ints(size_t n) {
  std::vector<int> vec;
  vec.reserve(n);
  for (auto i = 0; i < n; i++)
    vec.push_back(i);
  return vec;
}

std::vector<int> alternating_ints(size_t n) {
  std::vector<int> vec;
  vec.reserve(n);
  for (auto i = 0; i < n; i++)
    vec.push_back(i % 2 == 0 ? i : n - i);
  return vec;
}

std::vector<int> random_ints(size_t n) {
  std::vector<int> vec;
  vec.reserve(n);
  srand(n);
  for (auto i = 0; i < n; i++)
    vec.push_back(rand());
  return vec;
}

// Benchmarking in place partitioning
template <class T, size_t partition(std::vector<T> &, size_t, size_t),
          std::vector<T> generate(size_t)>
static void partition_in_place(benchmark::State &state) {
  for (auto _ : state) {
    state.PauseTiming();
    std::vector<T> workload(generate(state.range(0)));
    state.ResumeTiming();
    partition(workload, 0, workload.size());
    benchmark::DoNotOptimize(workload);
  }
}

// Benchmarking out of place (no including alloc time for aux vector)
template <class T,
          size_t partition(const std::vector<T> &, std::vector<T> &, size_t,
                           size_t),
          std::vector<T> generate(size_t)>
static void partition_out_of_place(benchmark::State &state) {
  for (auto _ : state) {
    state.PauseTiming();
    std::vector<T> workload(generate(state.range(0)));
    std::vector<T> aux(state.range(0));
    state.ResumeTiming();
    partition(workload, aux, 0, workload.size());
    benchmark::DoNotOptimize(aux);
  }
}

BENCHMARK(partition_in_place<int, hoare::partition, ordered_ints>)
    ->Range(8 * 1024, 64 * 1024);
BENCHMARK(partition_in_place<int, predicated_cracking::partition, ordered_ints>)
    ->Range(8 * 1024, 64 * 1024);
BENCHMARK(
    partition_out_of_place<int, out_of_place_cond::partition, ordered_ints>)
    ->Range(8 * 1024, 64 * 1024);
BENCHMARK(
    partition_out_of_place<int, out_of_place_pred::partition, ordered_ints>)
    ->Range(8 * 1024, 64 * 1024);

BENCHMARK(partition_in_place<int, hoare::partition, alternating_ints>)
    ->Range(8 * 1024, 64 * 1024);
BENCHMARK(
    partition_in_place<int, predicated_cracking::partition, alternating_ints>)
    ->Range(8 * 1024, 64 * 1024);
BENCHMARK(
    partition_out_of_place<int, out_of_place_cond::partition, alternating_ints>)
    ->Range(8 * 1024, 64 * 1024);
BENCHMARK(
    partition_out_of_place<int, out_of_place_pred::partition, alternating_ints>)
    ->Range(8 * 1024, 64 * 1024);

BENCHMARK(partition_in_place<int, hoare::partition, random_ints>)
    ->Range(8 * 1024, 64 * 1024);
BENCHMARK(partition_in_place<int, predicated_cracking::partition, random_ints>)
    ->Range(8 * 1024, 64 * 1024);
BENCHMARK(
    partition_out_of_place<int, out_of_place_cond::partition, random_ints>)
    ->Range(8 * 1024, 64 * 1024);
BENCHMARK(
    partition_out_of_place<int, out_of_place_pred::partition, random_ints>)
    ->Range(8 * 1024, 64 * 1024);

BENCHMARK_MAIN();
