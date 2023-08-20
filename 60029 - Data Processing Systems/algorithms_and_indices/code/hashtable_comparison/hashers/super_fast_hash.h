#pragma once

// Paul Hsieh's super fast hash
// Source: http://www.azillionmonkeys.com/qed/hash.html

#include <string>
#include <cstdint>

namespace Hash {
    inline uint16_t get16bits(const char* d) {
        return *reinterpret_cast<const uint16_t*>(d);
    }
    

    size_t SuperFast (const std::string& str) {
        if (str.empty()) return 0;
        const char* data = str.c_str();
        size_t len = str.size();
        uint32_t hash = len;
        uint32_t tmp;
        int rem = len & 3;
        len >>= 2;

        /* Main loop */
        for (;len > 0; len--) {
            hash  += get16bits (data);
            tmp    = (get16bits (data+2) << 11) ^ hash;
            hash   = (hash << 16) ^ tmp;
            data  += 2 * sizeof(uint16_t);
            hash  += hash >> 11;
        }

        switch (rem) {
            case 3: hash += get16bits (data);
                    hash ^= hash << 16;
                    hash ^= ((signed char)data[sizeof (uint16_t)]) << 18;
                    hash += hash >> 11;
                    break;
            case 2: hash += get16bits (data);
                    hash ^= hash << 11;
                    hash += hash >> 17;
                    break;
            case 1: hash += (signed char)*data;
                    hash ^= hash << 10;
                    hash += hash >> 1;
        }

        hash ^= hash << 3;
        hash += hash >> 5;
        hash ^= hash << 4;
        hash += hash >> 17;
        hash ^= hash << 25;
        hash += hash >> 6;

        // Note: SuperFastHash was designed for 32 bit hashes, we just zero-extend here
        return static_cast<size_t>(hash);
    }
}
