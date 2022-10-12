#include <thread>
#include <iostream>
#include <chrono>

int main() {
  using namespace std::chrono_literals; // to use the ms syntax

  std::cout << std::this_thread::get_id() << " will sleep now!" << std::endl;
  std::this_thread::sleep_for(200ms);

  std::cout << std::this_thread::get_id() << " has awoken!" << std::endl;
}