#pragma once
#include <cstddef>
#include <vector>

namespace predicated_cracking {

constexpr bool USE_CONDITIONS = false;

// INV: sort_vec.size() > 0
template <typename T>
size_t partition(std::vector<T> &sort_vec, size_t start, size_t end) {

  bool cmp = false;
  size_t left_ptr = start;
  size_t right_ptr = end - 1;
  T active = sort_vec[left_ptr];
  T backup = sort_vec[right_ptr];
  T pivot = sort_vec[(start + end) / 2]; // somewhat arbitrary pivot selection

  while (left_ptr < right_ptr) {

    // write active
    sort_vec[left_ptr] = active;
    sort_vec[right_ptr] = active;

    if constexpr (USE_CONDITIONS) {
      if (pivot > active) {
        left_ptr++;
        active = sort_vec[left_ptr];
      } else {
        right_ptr--;
        active = sort_vec[right_ptr];
      }
    } else {
      // compare and write
      cmp = pivot > active;

      // advance cursor
      left_ptr += cmp;
      right_ptr -= 1 - cmp;

      // backup phase
      active = cmp * sort_vec[left_ptr] + (1 - cmp) * sort_vec[right_ptr];
    }

    // swap active
    std::swap(active, backup);
  }

  sort_vec[left_ptr] = active;
  return left_ptr;
}

} // namespace predicated_cracking