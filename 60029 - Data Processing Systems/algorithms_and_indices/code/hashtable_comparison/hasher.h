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
using Hasher = const size_t (const K&);

template<typename K>
const size_t std_hash(const K& key) { return std::hash<K>{}(key); }

// A hasher that always returns 0 (many collisions)
template<typename K>
const size_t collision_hash(const K&) { return 0; }

// An unsafe hash, just uses the first few bytes of the object
template<typename K>
const size_t byte_hash(const K& key) {
    constexpr auto num_bytes = min(sizeof(K), sizeof(size_t));
    size_t hash = 0;
    uint8_t* bytes = reinterpret_cast<uint8_t*>(addressof(key));
    for (auto i = 0; i < num_bytes; i++) {
        hash += bytes[i] << (i * 8); 
    }
    return hash;
}


// To make your own hash:
// 1. Declare your templated hash function
template<typename K> const size_t my_hash(const K& key); 
// We could also define a default hash here, such as { return 0; // awful default hash! }

// 2. Specialize it for different types
template<> const size_t my_hash<int>   (const int& key)    { return static_cast<size_t>(key); }
template<> const size_t my_hash<bool>  (const bool& key)   { return key ? 0 : 42;             }
template<> const size_t my_hash<string>(const string& key) { return key.size() * 13;          }
