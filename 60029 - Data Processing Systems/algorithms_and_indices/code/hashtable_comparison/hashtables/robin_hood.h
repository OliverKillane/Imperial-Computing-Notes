#pragma once

#include "../hasher.h"
#include "../hashtable.h"
#include "../utils.h"

// RobinHood hashmap
// - Probing hashmap using linear probing
// - For each entry, we keep the distance from the original hash
// - When inserting, if the insert is further from the original hash than the 
//   entry it is in conflict with, swap them, continue to try and insert
// - Keeps distance 'from desired' / to original hash low 

// TODO: left as exercise for the reader (I'm aware this is cringe)

namespace HashMap {
    template<typename K, typename V, Hasher hasher>
    class RobinHood {
        public:
        bool insert(K, V) { return false;}
        V* find(const K&) noexcept { return nullptr; }
        bool contains(const K&) const noexcept { return false; }
        bool erase(const K&) noexcept { return false; }
        size_t size() const noexcept { return 0; }

        // Debug print
        friend std::ostream &operator<<(std::ostream &os, const RobinHood<K, V, hasher> & ht) {
            return os;
        }

        static_assert(IsHashMap<RobinHood<K, V, hasher>, K, V>, "not a hashmap");
    };
}
