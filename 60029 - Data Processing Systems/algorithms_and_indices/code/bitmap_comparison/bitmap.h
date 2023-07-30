#pragma once

#include <cstddef>
#include <utility>

namespace BitMap {
    
    // A concept for a bitvector
    // - should be empty by default
    template<typename T>
    concept IsBitMap = requires(T& t, const T& tc) {
        // set(index, value) -> changed?
        { t.set(std::declval<size_t>(), std::declval<bool>())} -> std::same_as<bool>;
        // get(index) -> value
        { tc.get(std::declval<size_t>()) } noexcept -> std::same_as<bool>;
    };
}

