#include <thread>
#include <iostream>

// function is static -> only within this file
static void some_func(const int& a) {
  std::cout << a << std::endl;
}

int main() {
    int a = 7;
    std::thread my_thread_a(some_func, a);
}

