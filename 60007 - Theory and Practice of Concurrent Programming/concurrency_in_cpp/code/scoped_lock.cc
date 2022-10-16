#include <mutex>
#include <iostream>


std::mutex m1, m2;

static void some_fun() {
    std::scoped_lock lock(m1, m2); // acquire lock on m1 and m2 (or any number of locks)

    std::cout << "Critical region here" << std::endl;

    // m1 and m2 are dropped here when the scoped lock is destroyed
}

int main() {
    some_fun();
}