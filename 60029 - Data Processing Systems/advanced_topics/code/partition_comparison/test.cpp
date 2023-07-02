#include <iostream>
#include "in_place_predicated.h"

using namespace predicated_cracking;

int main() {
    std::vector<int> is = {3, 2, 4, 2, 8, 1, 9, 3, 8, 1, 5, 0, 7, 5, 7};
    
    for (const auto& x : is) std::cout << x << ",";
    auto part = partition(is, 0, is.size());
    std::cout << std::endl;
    for (const auto& x : is) std::cout << x << ",";
    std::cout << std::endl << part;
}

