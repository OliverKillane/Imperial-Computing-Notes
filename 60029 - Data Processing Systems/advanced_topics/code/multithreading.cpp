#include <iostream>
#include <thread>
#include <vector>


template <size_t n>
void element_sum_threads(int64_t x[n], int64_t y[n], int64_t z[n]) {
  const auto no_threads = std::thread::hardware_concurrency();
  const auto n_per_thread =
      ((n - 1) / no_threads) + 1; // round-up integer division trick
  std::vector<std::thread> threads;
  for (auto index = 0; index < n; index += n_per_thread) {
    threads.emplace_back([&, index] {
      for (auto s = index; s < std::min(index + n_per_thread, n); s++)
        z[s] = x[s] + y[s];
    });
  }

  for (auto &t : threads)
    t.join();
}

int main() {
  int64_t x[10] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
  int64_t y[10] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
  int64_t z[10];
  element_sum_threads<10>(x, y, z);
  std::cout << std::thread::hardware_concurrency();

  for (const auto &e : z)
    std::cout << e << ", ";
}