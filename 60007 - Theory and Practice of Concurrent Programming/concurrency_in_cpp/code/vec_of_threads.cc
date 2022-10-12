#include <thread>
#include <vector>

static void some_func() {
    // do something
}

int main() {
    std::vector<std::thread> threads;

    // results in a copy
    for (int i; i < 10; i++) {
        threads.push_back(std::thread(some_func));
    }

    // allocated directly inside vector
    for (int i; i < 10; i++) {
        threads.emplace_back(some_func);
    }

    for (auto& t : threads) {
        t.join();
    }
}