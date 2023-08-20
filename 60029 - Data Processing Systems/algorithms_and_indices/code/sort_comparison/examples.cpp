#include "sorts/heapsort.h"

#include <iostream>
#include <vector>


constexpr auto intcomp = [](const int& a, const int& b) -> bool {return a < b;};

template<typename T>
void print_vec(const std::vector<T>& v) {
    for (const auto& x : v) {
        std::cout << x << " ";
    }
    std::cout << std::endl;
}

void demo_1() {
    std::vector<int> unsorted{9,7,8,6,5,5,6,4,5,3,1,4,3,1,2};
    std::cout << "Unsorted: ";
    print_vec(unsorted);
    for (size_t i = unsorted.size(); i > 0; i--) {
        siftDown<int, +intcomp>(unsorted, i - 1, unsorted.size());
    }

    std::cout << "Heapified: ";
    print_vec(unsorted);


    std::cout << "Sifting down:" << std::endl;
    for (size_t i = unsorted.size(); i > 1; i--) {
        swap(unsorted[0], unsorted[i - 1]);
        siftDown<int, +intcomp>(unsorted, 0, i - 1);
        print_vec(unsorted);
    }
}

int main() {
    demo_1();
}