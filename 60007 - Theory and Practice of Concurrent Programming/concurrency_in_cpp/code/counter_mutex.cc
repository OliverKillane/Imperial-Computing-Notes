#include <thread>
#include <iostream>
#include <mutex>
#include <vector>
#include <chrono>

int cnt;
std::mutex cnt_lock;

static void increment_cnt() {
  for (int i = 0; i < 10; i++) {
    std::this_thread::sleep_for(std::chrono::milliseconds(1));    
    cnt_lock.lock();
    cnt++;
    cnt_lock.unlock();
  }
}

int main() {
  std::vector<std::thread> threads;

  for (int i = 0; i < 100; i++) {
    threads.emplace_back(increment_cnt);
  }

  for (auto& t : threads) {
    t.join();
  }

  std::cout << "The counter is: " << cnt << std::endl;
}