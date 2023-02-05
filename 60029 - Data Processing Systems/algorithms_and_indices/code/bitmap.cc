#include <vector>
#include <cstddef>
#include <cstdint>
#include <iostream>

using namespace std;

// scans a vector of ints:
// - indexes each integer from LSB(0) to MSB(31)
// - does not consider endian-ness
// 100... 100... <=> [1,1]
vector<size_t> scan_bitmap(const vector<uint32_t>& bitvector) {
    vector<size_t> positions;
    size_t index = 0;
    for (auto elem : bitvector) {
        for (size_t small_index = 0; elem; small_index++, elem >>= 1) {
            if (elem & 1) {
                positions.push_back(index + small_index);
            }
        }
        index += 32;
    }
    return positions;
}
