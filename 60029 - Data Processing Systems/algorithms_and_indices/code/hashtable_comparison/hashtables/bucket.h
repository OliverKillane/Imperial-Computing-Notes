#pragma once

#include "../hashtable.h"

#include <vector>
#include <tuple>
#include <forward_list>
#include <algorithm>

#include "../hasher.h"

using namespace std;



// A bucket based hashmap
// - An array of buckets, bucket chosen by hash
// - Each bucket is a singly-linked list of (key, value) pairs
// - Ideally each bucket should be small (1 element) 
template<typename K, typename V, Hasher<K> hasher>
class BucketMap {
    vector<forward_list<tuple<K,V>>> _buckets;
    size_t _size;

    const size_t _get_index(const K& key) const noexcept {
        return hasher(key) % _buckets.size();
    }

public:
    bool insert(K&& key, V&& val) { 
        auto bucket = _buckets.at(_get_index(key));
        if (any_of(bucket.cbegin(), bucket.cend(), [&key](auto kv){return get<0>(kv) == key;})) {
            // already present in the map
            return false;
        } else {
            bucket.emplace_front(tuple {key, val});
            _size++;
            return true;
        }
    }

    V* find(const K& key) noexcept { 
        for (auto& [cmp_key, val] : _buckets.at(_get_index(key))) {
            if (key == cmp_key) {
                return &val;
            }
        }
        return nullptr;
     }

    bool contains(const K& key) const noexcept { 
        auto bucket = _buckets.at(_get_index(key));
        return any_of(bucket.cbegin(), bucket.cend(), [&key](auto kv){return get<0>(kv) == key;});
     }

    bool erase(const K& key) noexcept {
        auto bucket = _buckets.at(_get_index(key));
        auto prev = bucket.before_begin();
        for (auto it = bucket.begin(); it != bucket.end(); it++) {
            if (get<0>(*it) == key) {
                bucket.erase_after(prev);
                _size--;
                return true;
            }
            prev = it;
        }
        return false;
     }

     size_t size() const noexcept { return _size; }

    static_assert(HashMap<BucketMap, K, V>, "BucketMap is not a hashmap!");
};
