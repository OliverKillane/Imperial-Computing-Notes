#include <thread>

static void set_x(int& x) {
  x = 1;
}

static void wait_x(int& x) {
  while (x == 0);
}

int main() {
  int x = 0;
  std::thread t1(set_x, std::ref(x));
  std::thread t2(wait_x, std::ref(x));
  t1.join();
  t2.join();
}