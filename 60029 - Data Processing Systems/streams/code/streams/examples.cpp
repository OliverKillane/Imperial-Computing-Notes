#include "streams.h"

void example_1() {
  Output<int> console(std::cout);
  Project<int, int> mult(&console, [](auto i) { return i * 3; });
  Select<int> even(&mult, [](auto &i) { return i % 2 == 0; });
  UserInput<int> user(&even, std::cin);

  user.run();
}

void example_2() {
  Output<float> console(std::cout);
  WindowSumAggregator sum(&console, 4);
  Project<int, float> mult(&sum, [](auto i) { return static_cast<float>(i); });
  Select<int> even(&mult, [](auto &i) { return i % 2 == 0; });
  UserInput<int> user(&even, std::cin);

  user.run();
}

int intmax(int &a, int &b) { return std::max(a, b); }

void example_3() {
  Output<int> console(std::cout);
  WindowTwoStackAggregator<int, intmax> maxints(&console, 3);
  UserInput<int> user(&maxints, std::cin);

  user.run();
}

int main() {
  // example_1();
  // example_2();
  example_3();
}