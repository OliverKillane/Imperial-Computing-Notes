#include <mutex>
#include <iostream>
#include <functional>

class Defer {
  private:
    std::function<void(void)> function_;

  public:
    Defer(std::function<void(void)> fun) : function_(fun) {}
    ~Defer() {
      function_();
    }
};


int main() {
  std::mutex m;

  Defer lock([&m] () {
    m.unlock();
    std::cout << "unlocked" << std::endl;}
  );

  std::cout << "hello world" << std::endl;
}