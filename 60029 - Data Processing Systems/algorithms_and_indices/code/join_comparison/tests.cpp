#include "table.h"

#include "joins/nested_loop.h"
#include "joins/sort_merge.h"
#include "joins/unique_sort_merge.h"
#include "joins/hash.h"
#include "joins/unique_hash.h"

#include "gtest/gtest.h"

#include <vector>

using namespace std;

// "UUhhh, using macros for testing all algos? Kinda cringe"
// Yes. But the other way is verbose -> impossible.
// - I would need to parameterize tests by a non-type template template
//   parameter
// - google test uses TYPED_TEST for template params, but they must be types,
//   and template template is not allowed!
// - I could wrap each join in a class, which has a templated method for the
//   join, but that is more
//   effort than just saying 'screw it - its macroing time'

#define EMPTY_TEST(JOIN_ALGO)                                                  \
  TEST(JOIN_ALGO, EmptyJoin) {                                                 \
    Table<int, int> input{.name = "test", .cols = {"a", "b"}, .rows = {}};     \
    auto answer = JOIN_ALGO<0, 0>(input, input);                               \
    auto expected = join_empty<0, 0>(input, input);                            \
    answer.sort_rows();                                                        \
    expected.sort_rows();                                                      \
    EXPECT_EQ(expected, answer);                                               \
  }

#define UNIQUE_TEST(JOIN_ALGO)                                                 \
  TEST(JOIN_ALGO, UniqueJoin) {                                                \
    Table<int, int> input{                                                     \
        .name = "test", .cols = {"a", "b"}, .rows = {{1, 1}, {2, 2}, {3, 3}}}; \
    auto answer = JOIN_ALGO<0, 0>(input, input);                               \
    auto expected = join_empty<0, 0>(input, input);                            \
    expected.rows = {{1, 1, 1, 1}, {2, 2, 2, 2}, {3, 3, 3, 3}};                \
    answer.sort_rows();                                                        \
    expected.sort_rows();                                                      \
    EXPECT_EQ(expected, answer);                                               \
  }

#define DUPLICATE_ROW_TEST(JOIN_ALGO)                                          \
  TEST(JOIN_ALGO, DuplicatedRow) {                                             \
    Table<int, int> input{.name = "test",                                      \
                          .cols = {"a", "b"},                                  \
                          .rows = {{1, 1}, {2, 2}, {2, 3}, {3, 3}}};           \
    auto answer = JOIN_ALGO<0, 0>(input, input);                               \
    auto expected = join_empty<0, 0>(input, input);                            \
    expected.rows = {{1, 1, 1, 1}, {2, 2, 2, 2}, {2, 2, 2, 3},                 \
                     {2, 3, 2, 2}, {2, 3, 2, 3}, {3, 3, 3, 3}};                \
    answer.sort_rows();                                                        \
    expected.sort_rows();                                                      \
    EXPECT_EQ(expected, answer);                                               \
  }

#define DUPLICATE_AT_END_TEST(JOIN_ALGO)                                       \
  TEST(JOIN_ALGO, DuplicatedRowAtEnd) {                                        \
    Table<int, int> input{                                                     \
        .name = "test", .cols = {"a", "b"}, .rows = {{1, 1}, {2, 2}, {2, 3}}}; \
    auto answer = JOIN_ALGO<0, 0>(input, input);                               \
    auto expected = join_empty<0, 0>(input, input);                            \
    expected.rows = {                                                          \
        {1, 1, 1, 1}, {2, 2, 2, 2}, {2, 2, 2, 3}, {2, 3, 2, 2}, {2, 3, 2, 3}}; \
    answer.sort_rows();                                                        \
    expected.sort_rows();                                                      \
    EXPECT_EQ(expected, answer);                                               \
  }

EMPTY_TEST(sort_merge_join)
UNIQUE_TEST(sort_merge_join)
DUPLICATE_ROW_TEST(sort_merge_join)
DUPLICATE_AT_END_TEST(sort_merge_join)

EMPTY_TEST(unique_sort_merge_join)
UNIQUE_TEST(unique_sort_merge_join)
// does not work for duplicate rows

EMPTY_TEST(hash_join)
UNIQUE_TEST(hash_join)
DUPLICATE_ROW_TEST(hash_join)
DUPLICATE_AT_END_TEST(hash_join)

EMPTY_TEST(unique_hash_join)
UNIQUE_TEST(unique_hash_join)
// does not work for duplicate rows

EMPTY_TEST(nested_loop_join)
UNIQUE_TEST(nested_loop_join)
DUPLICATE_ROW_TEST(nested_loop_join)
DUPLICATE_AT_END_TEST(nested_loop_join)
