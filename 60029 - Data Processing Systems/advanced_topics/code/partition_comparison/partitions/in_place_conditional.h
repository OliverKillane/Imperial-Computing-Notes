#pragma once
#include <cstddef>
#include <vector>

namespace hoare {
// INV: sort_vec.size() > 0
template <typename T>
size_t partition(std::vector<T> &sort_vec, size_t start, size_t end) {
  // get pivot
  T pivot = sort_vec[start];
  size_t count = 0;

  // determine where to partition / where to place pivot value
  for (size_t i = start + 1; i < end; i++) {
    if (sort_vec[i] <= pivot)
      count++;
  }

  // swap pivot into place, will partition around pivot
  size_t pivotIndex = start + count;
  std::swap(sort_vec[pivotIndex], sort_vec[start]);

  // start pointers i & j at ends of range
  size_t i = start, j = end - 1;

  // advance pointers, swap and partition
  while (i < pivotIndex && j > pivotIndex) {
    while (sort_vec[i] <= pivot)
      i++;
    while (sort_vec[j] > pivot)
      j--;

    if (i < pivotIndex && j >= pivotIndex) {
      std::swap(sort_vec[i], sort_vec[j]);
      i++;
      j--;
    }
  }

  return pivotIndex;
}
} // namespace hoare