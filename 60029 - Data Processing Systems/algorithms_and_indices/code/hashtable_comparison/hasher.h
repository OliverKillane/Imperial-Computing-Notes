#pragma once

#include <functional>
#include <cstddef>
#include <algorithm>
#include <array>
#include <cstdint>
using namespace std;

// A basic hasher takes some key to hash, and the maximum has allowed (e.g 
// slots or buckets in the hashtable)
template<typename K>
using Hasher = size_t (const K&);

// To make your own hash:
// 0. Create a new file hashers/<name>.h
namespace Hash {
    // 1. Declare your templated hash function
    template<typename K> size_t my_hash(const K& key); 
    // We could also define a default hash here, such as { return 0; // awful default hash! }

    // 2. Specialize it for different types
    template<> size_t my_hash<int>   (const int& key)    { return static_cast<size_t>(key); }
    template<> size_t my_hash<bool>  (const bool& key)   { return key ? 0 : 42;             }
    template<> size_t my_hash<string>(const string& key) { return key.size() * 13;          }
}