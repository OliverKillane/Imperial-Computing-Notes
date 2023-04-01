#include <vector>

template <typename T, bool comp(T, T)>
std::size_t partition(std::vector<T>& sort_vec, std::size_t start, std::size_t end) {
  T pivot = sort_vec[start];
  std::size_t count = 0;

  for(std::size_t i = start + 1; i < end; i++) {
    if (comp(sort_vec[i], pivot)) count++;
  }

  std::size_t pivotIndex = start + count;
  std::swap(sort_vec[pivotIndex], sort_vec[start]);
  std::size_t i = start, j = end - 1;

  while(i < pivotIndex && j > pivotIndex) {
    while(comp(sort_vec[i], pivot)) i++;
    while(!comp(sort_vec[j], pivot)) j--;

    if(i < pivotIndex && j >= pivotIndex) {
      std::swap(sort_vec[i], sort_vec[j]);
      i++;
      j--;
    }
  }

  return pivotIndex;
}

template <typename T, bool comp(T, T)>
void quicksort_helper(std::vector<T>& sort_vec, std::size_t start, std::size_t end) {
  if(start + 1 >= end) return;

  std::size_t p = partition<T, comp>(sort_vec, start, end);
  quicksort_helper<T, comp>(sort_vec, start, p);
  quicksort_helper<T, comp>(sort_vec, p + 1, end);
}

template <typename T, bool comp(T, T)> void quicksort(std::vector<T>& sort_vec) {
  quicksort_helper<T, comp>(sort_vec, 0, sort_vec.size());
}
