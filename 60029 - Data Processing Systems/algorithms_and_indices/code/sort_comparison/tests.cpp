#include "sorts/heapsort.h"
#include "sorts/mergesort.h"
#include "sorts/quicksort.h"


#include "generate.h"

#include "gtest/gtest.h"

#include <vector>

using namespace std;

constexpr auto intcomp = [](const int &a, const int &b) -> bool {
  return a > b;
};

// Cannot pass non-type template params to typed tests, so we wrap with a type
// associated with the sort.
template <auto sort> struct Sorter {
  static constexpr auto s = sort;
};

using Sorts = ::testing::Types<Sorter<heapsort<int, +intcomp>>,
                               Sorter<quicksort<int, +intcomp>>,
                               Sorter<mergesort<int, +intcomp>>>;

template <class Sorter> class SortTest : public testing::Test {};

TYPED_TEST_SUITE(SortTest, Sorts);

TYPED_TEST(SortTest, EmptyList) {
  vector<int> input{};
  vector<int> answer{};
  TypeParam::s(input);
  EXPECT_EQ(answer, answer);
}

TYPED_TEST(SortTest, OnetoFive) {
  vector<int> input{5, 4, 3, 2, 1};
  vector<int> answer{1, 2, 3, 4, 5};
  TypeParam::s(input);
  EXPECT_EQ(answer, answer);
}
