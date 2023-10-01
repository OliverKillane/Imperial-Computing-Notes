#include "partitions/in_place_conditional.h"
#include "partitions/in_place_predicated.h"
#include "partitions/out_of_place_conditional.h"
#include "partitions/out_of_place_predicated.h"
#include <cstddef>
#include <iostream>
#include <vector>

template <typename T> void print_vec(const std::vector<T> &v) {
  for (const auto &x : v)
    std::cout << x << ",";
  std::cout << std::endl;
}

void example_1() {
  std::vector<int> is = {2, 3, 12, 5, 6, 7, 34, 3, 2, 1, 3, 5, 7, 23};
  // std::vector<int> is = {
  //     2, 1, 2, 6, 7, 34, 3, 5, 12, 3, 5, 7, 3, 23,
  // };

  print_vec(is);
  auto part = predicated_cracking::partition(is, 0, is.size());
  print_vec(is);
  std::cout << "partition at vec[" << part << "] = " << is[part] << std::endl;
}

void example_2() {
  std::vector<int> is = {7};
  std::vector<int> ans(is.size());

  print_vec(is);
  auto part = out_of_place_cond::partition(is, ans, 0, is.size());
  print_vec(ans);
  std::cout << "partition at vec[" << part << "] = " << ans[part] << std::endl;
}

int main() {
  example_1();
  example_2();
}
