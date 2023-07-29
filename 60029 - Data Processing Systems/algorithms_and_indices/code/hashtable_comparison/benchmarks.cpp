#include "hashtables/bucket.h"
#include "hashtables/std_unordered_map.h"
#include "hashtables/probing.h"

#include "hashers/const_hash.h"
#include "hashers/std_hash.h"
#include "hashers/super_fast_hash.h"

#include <benchmark/benchmark.h>

#include <string>

std::string generate_random_string(size_t len) {
    std::string str(len, '\0');
    for (size_t i = 0; i < len; i++) {
        str[i] = 97 + std::rand() % 26;
    }
    return str;
}

// Benchmarking time taken to hash a random string of n characters
// - randomness is unlikely to result in difference, but is representative
template<Hasher<std::string> hash>
static void hash_string(benchmark ::State &state) {
    for (auto _ : state) {
        for (auto i = 0; i < 100; i++) {
            state.PauseTiming();
            std::string workload = generate_random_string(state.range(0)); 
            state.ResumeTiming();
            benchmark::DoNotOptimize(hash(workload));
        }
    }
}

BENCHMARK(hash_string<Hash::STD<std::string>>)->Range(1, 128);
BENCHMARK(hash_string<Hash::SuperFast>)->Range(1, 128);

// Benchmarking random inserts to the hashmap
// - Using integers (want to benchmark the hashmap, rather than hasher)
// - Integers are not unique - hashmap need to check for duplicates. 
template<typename HashMapIntsChar>
static void hashmap_random_insert(benchmark ::State &state) {
    for (auto _ : state) {
        HashMapIntsChar m;
        for (auto i = 0; i < state.range(0); i++) {
            m.insert(rand(), '0');
        }
    }
}

// NOTE: the commas in the template mean they are technically multiple args
#define BENCH_RAND_INSERT(...) BENCHMARK(hashmap_random_insert<__VA_ARGS__>)->Range(1 << 6, 1 << 10);

BENCH_RAND_INSERT(HashMap::STD<int, char, Hash::STD<int>>);
BENCH_RAND_INSERT(HashMap::Buckets<int, char, Hash::STD<int>>);
BENCH_RAND_INSERT(HashMap::Probing<int, char, HashMap::Probes::Linear<int, Hash::STD<int>>>);
// BENCH_RAND_INSERT(HashMap::Probing<int, char, HashMap::Probes::Quadratic<int, Hash::STD<int>>>);

// Benchmarking random inserts with conflicts
// - Using Hash::Const to make conflicts
#define BENCH_RAND_CONFLICT(...) BENCHMARK(hashmap_random_insert<__VA_ARGS__>)->Range(1 << 3, 1 << 6);

BENCH_RAND_CONFLICT(HashMap::STD<int, char, Hash::Const<int>>);
BENCH_RAND_CONFLICT(HashMap::Buckets<int, char, Hash::Const<int>>);
BENCH_RAND_CONFLICT(HashMap::Probing<int, char, HashMap::Probes::Linear<int, Hash::Const<int>>>);
// BENCH_RAND_CONFLICT(HashMap::Probing<int, char, HashMap::Probes::Quadratic<int, Hash::Const<int>>>);

BENCHMARK_MAIN();