#pragma once
#include <concepts>
#include <cstddef>
#include <vector>

namespace out_of_place_pred {
// INV: input_vec.size() > 0
template <std::copy_constructible T>
size_t partition(const std::vector<T> &input_vec, std::vector<T> &output_vec,
                 size_t start, size_t end) {
  const T &pivot = input_vec[(start + end) / 2];
  size_t left_index = start;
  size_t right_index = end - 1;

  for (auto i = start; i < end; i++) {
    output_vec[left_index] = input_vec[i];
    output_vec[right_index] = input_vec[i];

    // increment using boolean, if not incremented, value is overwritten on
    // the next iteration of the loop
    left_index += input_vec[i] < pivot;
    right_index -= input_vec[i] >= pivot;
  }

  return left_index;
}
} // namespace out_of_place_pred