#include "table.h"
#include "generate.h"

#include "joins/nested_loop.h"
#include "joins/sort_merge.h"
#include "joins/unique_sort_merge.h"
#include "joins/hash.h"
#include "joins/unique_hash.h"

#include <benchmark/benchmark.h>

tuple<int> increasing  (size_t i) {return make_tuple(i);}
tuple<int> decreasing  (size_t i) {return make_tuple(-i);}
tuple<int> alternating (size_t i) {return i % 2 == 0 ? increasing(i) : decreasing(i);}
tuple<int> random      (size_t i) {return make_tuple(rand());}
// TODO: the number of duplicates has a huge effect, so need to make a generator that expresses some 'duplicateness'

// Benchmark(join, left size, right size, generate)
template<Table<int, int> join(const Table<int>&, const Table<int>&), Gen<int> gen>
static void join_simple(benchmark::State &state) {
  for (auto _ : state) {
    state.PauseTiming();
    auto left = create_table<int>::with_gen<gen>(state.range(0));
    auto right = create_table<int>::with_gen<gen>(state.range(1));
    state.ResumeTiming();
    join(left, right);
  }
}

// NOTE: Below are waaay to many benchmarks to be useful. Select some property that interests you, 
//       and restrict the benchmarks to that (e.g size of left table for hash join)

#define SIMPLE_BENCH(JOIN_ALGO, GEN_ALGO) BENCHMARK(join_simple<JOIN_ALGO<0, 0>, GEN_ALGO>)->ArgsProduct({{10, 100, 1000, 10000}, {20, 40, 60, 80}})

// SIMPLE_BENCH(hash_join,              increasing);
// SIMPLE_BENCH(unique_hash_join,       increasing);
// SIMPLE_BENCH(nested_loop_join,       increasing);
// SIMPLE_BENCH(sort_merge_join,        increasing);
// SIMPLE_BENCH(unique_sort_merge_join, increasing);

// SIMPLE_BENCH(hash_join,              decreasing);
// SIMPLE_BENCH(unique_hash_join,       decreasing);
// SIMPLE_BENCH(nested_loop_join,       decreasing);
// SIMPLE_BENCH(sort_merge_join,        decreasing);
// SIMPLE_BENCH(unique_sort_merge_join, decreasing);

// SIMPLE_BENCH(hash_join,              alternating);
// SIMPLE_BENCH(unique_hash_join,       alternating);
// SIMPLE_BENCH(nested_loop_join,       alternating);
// SIMPLE_BENCH(sort_merge_join,        alternating);
// SIMPLE_BENCH(unique_sort_merge_join, alternating);

// SIMPLE_BENCH(hash_join,              random);
// SIMPLE_BENCH(unique_hash_join,       random);
// SIMPLE_BENCH(nested_loop_join,       random);
// SIMPLE_BENCH(sort_merge_join,        random);
// SIMPLE_BENCH(unique_sort_merge_join, random);


// Sort merge joins are dependent on their sort, which is affected by the order 
// of input data, here we are in-part benchmarking the cpp std::sort
#define BENCH_SORT_MERGE(GEN_ALGO) BENCHMARK(join_simple<sort_merge_join<0, 0>, GEN_ALGO>)->ArgsProduct({{1000}, {1000}})

BENCH_SORT_MERGE(increasing);
BENCH_SORT_MERGE(decreasing);
BENCH_SORT_MERGE(alternating);
BENCH_SORT_MERGE(random);      // much slower!

BENCHMARK_MAIN();
