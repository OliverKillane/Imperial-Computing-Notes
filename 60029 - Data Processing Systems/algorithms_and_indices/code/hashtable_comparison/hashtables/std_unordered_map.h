#pragma once


#include "../hashtable.h"
#include "../utils.h"

#include <unordered_map>
#include <iostream>

// A wrapper for std::unordered_map

namespace HashMap {

    template<typename K, typename V>
    class STD {
        std::unordered_map<K, V> _map;

    public:
        bool insert(K key, V value) { 
            return _map.emplace(std::move(key), std::move(value)).second;
        }

        V* find(const K& key) noexcept { 
            auto it = _map.find(key);
            if (it != _map.cend()) {
                return &(it->second);
            } else {
                return nullptr;
            }
        }

        bool contains(const K& key) const noexcept { 
            return _map.contains(key); 
        }

        bool erase(const K& key) noexcept { 
            return _map.erase(key) > 0; 
        }
        size_t size() const noexcept { return _map.size(); }

        friend std::ostream &operator<<(std::ostream &os, const STD<K, V> & ht) {
            os << "Hash Table: " << type<STD<K, V>>() << std::endl;
            os << "Size: " << ht._map.size() << std::endl;
            os << "Buckets: " << ht._map.bucket_count() << std::endl;
            for (auto i = 0; i < ht._map.bucket_count(); i++) {
                os << i << ": ";
                if (ht._map.bucket_size(i) == 0) {
                    os << "<empty>";
                } else {
                    for (auto it = ht._map.cbegin(i); it != ht._map.cend(i); it++) {
                        os << "-> " << "{" << it->first << ":" << it->second << "}";
                    }
                }
                os << std::endl;
            }
            return os;
        }

        static_assert(IsHashMap<STD<K, V>, K, V>, "not a hashmap");
    };
}