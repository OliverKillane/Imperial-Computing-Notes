#include "hashtables/bucket.h"
#include "hashtables/std_unordered_map.h"
#include "hashtables/probing.h"

#include "hashers/const_hash.h"
#include "hashers/std_hash.h"
#include "hashers/super_fast_hash.h"

#include <benchmark/benchmark.h>

// Benchmarks for hashers




BENCHMARK_MAIN();