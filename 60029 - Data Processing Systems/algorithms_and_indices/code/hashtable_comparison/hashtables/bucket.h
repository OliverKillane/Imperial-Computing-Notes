#pragma once

#include "../hashtable.h"

#include <vector>
#include <tuple>
#include <forward_list>
#include <algorithm>
#include <exception>
#include <iostream>

#include "../hasher.h"
#include "../utils.h"

using namespace std;

// A bucket based hashmap
// - An array of buckets, bucket chosen by hash
// - Each bucket is a singly-linked list of (key, value) pairs
// - Ideally each bucket should be small (1 element) 
template<typename K, typename V, Hasher<K> hasher>
class BucketMap {
    vector<forward_list<tuple<K,V>>> _buckets;
    size_t _size = 0;

    const size_t _get_index(const K& key) const noexcept {
        return hasher(key) % _buckets.size();
    }

    bool _resize_policy() const noexcept {
        // if on average, more than two per bucket - resize.
        // is this a good policy? ==> depends on (hasher, cost of resize)
        return _size / _buckets.size() > 2;
    }

    void resize() noexcept {
        vector<forward_list<tuple<K,V>>> old_buckets(_buckets.size() * 2);
        for (auto& bucket : old_buckets) {
            // implement efficiently (std::forward_list<T>.splice_after)
        }
    }

public:
    BucketMap(size_t initial_buckets = 16) : _buckets(initial_buckets) {
        if (initial_buckets < 1) {
            throw std::invalid_argument("initial buckets must be larger than zero");
        }
    }

    bool insert(K&& key, V&& val) { 
        auto& bucket = _buckets.at(_get_index(key));
        if (any_of(bucket.cbegin(), bucket.cend(), [&key](auto kv){return get<0>(kv) == key;})) {
            // already present in the map
            return false;
        } else {
            bucket.emplace_front(tuple {key, val});
            _size++;
            // add resize policy check and resize
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
        const auto& bucket = _buckets.at(_get_index(key));
        return any_of(bucket.cbegin(), bucket.cend(), [&key](auto kv){return get<0>(kv) == key;});
     }

    bool erase(const K& key) noexcept {
        auto& bucket = _buckets.at(_get_index(key));
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

     friend ostream &operator<<(ostream &os, const BucketMap<K, V, hasher> & ht) {
        os << "Hash Table: " << type<BucketMap<K, V, hasher>>() << endl;
        os << "Size: " << ht.size() << endl;
        os << "Buckets: " << ht._buckets.size() << endl;
        for (auto i = 0; i < ht._buckets.size(); i++) {
            const auto& bucket = ht._buckets[i];
            os << i << ": ";
            if (bucket.empty()) {
                os << "<empty>";
            } else {
                for (const auto& [key, val] : bucket) {
                    os << "-> " << "{" << key << ":" << val << "}";
                }
            }
            os << endl;
        }
        return os;
    }

    static_assert(HashMap<BucketMap, K, V>, "BucketMap is not a hashmap!");
};
