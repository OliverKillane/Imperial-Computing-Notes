#pragma once


#include "../hashtable.h"
#include "../utils.h"

#include <unordered_map>
#include <iostream>

using namespace std;


template<typename K, typename V>
class STLUnorderedMap {
    unordered_map<K, V> _map;

public:
    bool insert(K&& key, V&& value) { 
        return _map.emplace(key, value).second;
    }

    V* find(const K& key) noexcept { 
        auto it = _map.find(key);
        if (it != _map.cend()) {
            return *it;
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

    friend ostream &operator<<(ostream &os, const STLUnorderedMap<K, V> & ht) {
        os << "Hash Table: " << type<STLUnorderedMap<K, V>>() << endl;
        os << "Size: " << ht._map.size() << endl;
        os << "Buckets: " << ht._map.bucket_count() << endl;
        for (auto i = 0; i < ht._map.bucket_count(); i++) {
            os << i << ": ";
            if (ht._map.bucket_size(i) == 0) {
                os << "<empty>";
            } else {
                for (auto it = ht._map.cbegin(i); it != ht._map.cend(i); it++) {
                    os << "-> " << "{" << it->first << ":" << it->second << "}";
                }
            }
            os << endl;
        }
        return os;
    }

    static_assert(HashMap<STLUnorderedMap<K, V>, K, V>, "not a hashmap");
};
