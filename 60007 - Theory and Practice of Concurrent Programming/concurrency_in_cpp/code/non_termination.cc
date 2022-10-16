#include <thread>

static void do_nothing(int& x) {
  x = 1;
}

static void wait_forever(int& x) {
  while (x == 0);
}

int main() {
  int x = 0;
  std::thread t1(do_nothing, std::ref(x));
  std::thread t2(wait_forever, std::ref(x));
  t1.join();
  t2.join();
}

