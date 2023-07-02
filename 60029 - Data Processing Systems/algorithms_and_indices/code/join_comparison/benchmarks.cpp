#include "table.h"

#include "joins/nested_loop.h"
#include "joins/sort_merge.h"
#include "joins/unique_sort_merge.h"
#include "joins/hash.h"

#include <benchmark/benchmark.h>

BENCHMARK_MAIN();