#pragma once

#include <iostream>
#include <vector>

#include "../bitmap.h"


// Not a 'bitvector' but rather a bitmap implemented as a vector.
// - resize is expensive & will cause spikes on access.
// - this implementation does not allow the custom allocators :(
namespace BitMap {
    class BVec {
        std::vector<bool> _vec;

    public:
        BVec(size_t reserve_size = 0) {
            _vec.reserve(reserve_size);
        }

        bool set(size_t idx, bool val) {
            if (idx >= _vec.size()) {
                _vec.resize(idx + 1, false);
            }

            bool prev = _vec[idx];
            _vec[idx] = val;
            return prev != val;
        }

        bool get(size_t idx) const noexcept {
            if (idx >= _vec.size()) {
                return false;
            } else {
                return _vec[idx];
            }
        }

        friend std::ostream &operator<<(std::ostream &os, const BVec & bv) {
            std::cout << "Bitvector ~ capacity: " << bv._vec.size() << std::endl;
            for (size_t idx = 0; idx < bv._vec.size(); idx++) {
                std::cout << idx << ": " << (bv._vec[idx] ? "true" : "false") << std::endl;
            }
            std::cout << bv._vec.size() << "... : false" << std::endl;
            return os;
        }
    };
    static_assert(IsBitMap<BVec>, "not a bitmap");
}