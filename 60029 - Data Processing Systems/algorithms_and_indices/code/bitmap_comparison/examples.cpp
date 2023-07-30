#include "bitmap.h"
#include "bitmaps/bitvector.h"

void example_1() {
    BitMap::BVec bv;

    std::cout << "originally is" << std::endl 
              << bv << std::endl;

    for (size_t idx : {0,3,2,100}) {
        std::cout << "Set [" << idx << "] to true" << std::endl;
        bv.set(idx, true);
        std::cout << bv << std::endl; 
    }
}

int main() {
    example_1();
}


