#pragma once

#include "../hashtable.h"
#include <unordered_map>

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

    static_assert(HashMap<STLUnorderedMap<K, V>, K, V>, "not a hashmap");
};
