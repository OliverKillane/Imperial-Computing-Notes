#pragma once

#include <cstddef>
#include <functional>

// A wrapper for the normal stl

namespace Hash {
    template<typename K>
    size_t STD(const K& key) { return std::hash<K>{}(key); }
}