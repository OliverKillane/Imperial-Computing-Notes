#pragma once

#include <cstddef>
#include <cstdint>
#include <algorithm>

// An unsafe hash that uses the raw bytes provided to determine the hash
// - Unsafe (e.g apply to identical strings of different addresses -> pointers 
//   produce different hashes).
namespace hash {
    template<typename K>
    const size_t Bytes(const K& key) {
        constexpr auto num_bytes = min<K>(sizeof(K), sizeof(size_t));
        size_t hash = 0;
        uint8_t* bytes = reinterpret_cast<uint8_t*>(addressof(key));
        for (auto i = 0; i < num_bytes; i++) {
            hash += bytes[i] << (i * 8); 
        }
        return hash;
    }
}