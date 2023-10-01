#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include <cstddef>
#include <type_traits>
#include <variant>
#include <vector>

#include "partitions/in_place_conditional.h"
#include "partitions/in_place_predicated.h"
#include "partitions/out_of_place_conditional.h"
#include "partitions/out_of_place_predicated.h"

#include <iostream>

void check_partitioned(const std::vector<int> &orig,
                       const std::vector<int> &part, size_t part_at) {
  EXPECT_THAT(orig, ::testing::UnorderedElementsAreArray(part));

  // the
  auto part_at_val = part[part_at];
  auto top_min =
      *std::min_element(std::next(part.begin(), part_at), part.end());
  auto bot_max =
      *std::max_element(part.begin(), std::next(part.begin(), part_at));
  EXPECT_LE(bot_max, top_min);
}

using inplace = size_t(std::vector<int> &, size_t, size_t);
using outplace = size_t(const std::vector<int> &, std::vector<int> &, size_t,
                        size_t);

void partition_check(outplace fn, std::vector<int> vals) {
  std::vector<int> partitioned(vals.size());
  auto part_at = fn(vals, partitioned, 0, vals.size());
  check_partitioned(vals, partitioned, part_at);
}

void partition_check(inplace fn, std::vector<int> vals) {
  std::vector<int> orig = vals;
  auto part_at = fn(vals, 0, vals.size());
  check_partitioned(orig, vals, part_at);
}

#define NEW_TEST(PARTITION)                                                    \
  TEST(PARTITION, Single) { partition_check(PARTITION::partition, {1}); }      \
  TEST(PARTITION, OrderedAsc) {                                                \
    partition_check(PARTITION::partition, {1, 2, 3, 4, 5, 6});                 \
  }                                                                            \
  TEST(PARTITION, OrderedDesc) {                                               \
    partition_check(PARTITION::partition, {6, 5, 4, 3, 2, 1});                 \
  }                                                                            \
  TEST(PARTITION, AllSame) {                                                   \
    partition_check(PARTITION::partition, {1, 1, 1, 1, 1, 1});                 \
  }                                                                            \
  TEST(PARTITION, Large) {                                                     \
    partition_check(PARTITION::partition,                                      \
                    {2, 3, 12, 5, 6, 7, 34, 3, 2, 1, 3, 5, 7, 23});            \
  }

NEW_TEST(hoare)
NEW_TEST(predicated_cracking)
NEW_TEST(out_of_place_cond)
NEW_TEST(out_of_place_pred)