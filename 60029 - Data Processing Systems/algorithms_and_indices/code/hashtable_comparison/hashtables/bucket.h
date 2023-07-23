#pragma once

#include "../hashtable.h"

#include <vector>
#include <tuple>
#include <algorithm>
#include <exception>
#include <memory>
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

    struct BucketNode {
        K key;
        V value;
        BucketNode* next;
    };

    vector<BucketNode*> _buckets;
    size_t _size;

    const size_t _get_index(const K& key) const noexcept {
        return hasher(key) % _buckets.size();
    }

    bool _resize_policy() const noexcept {
        // if on average, more than two per bucket - resize.
        // is this a good policy? ==> depends on (hasher, cost of resize)
        return _size / _buckets.size() > 2;
    }

    void _resize() noexcept {
        vector<BucketNode*> old_buckets(_buckets.size() * 2);
        std::swap(old_buckets, _buckets);
        for (auto& bucket : old_buckets) {
            for (auto curr = bucket; curr;) {
                BucketNode*& dest = _buckets.at(_get_index(curr->key));
                BucketNode* next = curr->next;
                curr->next = dest;
                dest = curr;
                curr = next;
            }
        }
    }

public:
    // INV: initial_buckets > 0 
    BucketMap(size_t initial_buckets = 16) : _buckets(initial_buckets), _size(0) {}

    bool insert(K key, V val) {
        if (_resize_policy()) _resize();
        BucketNode*& bucket = _buckets.at(_get_index(key));
        for (const BucketNode* b = bucket; b; b = b->next) {
            if (b->key == key) return false;
        }
        bucket = new BucketNode{ .key=std::move(key), .value=std::move(val), .next=bucket };
        _size++;
        return true;
    }

    V* find(const K& key) noexcept { 
        for (BucketNode* b = _buckets.at(_get_index(key)); b; b = b->next) {
            if (b->key == key) return &b->value;
        }
        return nullptr;
     }

    bool contains(const K& key) const noexcept { 
        for (const BucketNode* b = _buckets.at(_get_index(key)); b; b = b->next) {
            if (b->key == key) return true;
        }
        return false;
     }

    bool erase(const K& key) noexcept {
        BucketNode*& first_node = _buckets.at(_get_index(key));

        if (first_node) {
            if (first_node->key == key) {
                BucketNode* next_node = first_node->next;
                delete first_node;
                first_node = next_node;
                _size--;
                return true;
            } else {
                BucketNode* prev = first_node;
                for (BucketNode* curr = prev->next; curr; prev = curr, curr = curr->next) {
                    if (curr->key == key) {
                        prev->next = curr->next;
                        delete curr;
                        _size--;
                        return true;
                    }
                }
                return false;
            }
        } else {
            return false;
        }
     }

     size_t size() const noexcept { return _size; }

     friend ostream &operator<<(ostream &os, const BucketMap<K, V, hasher> & ht) {
        os << "Hash Table: " << type<BucketMap<K, V, hasher>>() << endl;
        os << "Size: " << ht.size() << endl;
        os << "Buckets: " << ht._buckets.size() << endl;
        for (size_t i = 0; i < ht._buckets.size(); i++) {
            BucketNode* first_node = ht._buckets[i];
            os << i << ": ";
            if (first_node) {
                for (BucketNode* b = first_node; b; b = b->next) {
                    os << "-> " << "{" << b->key << ":" << b->value << "}";
                }
            } else {
                os << "<empty>";
            }
            os << endl;
        }
        return os;
    }

    static_assert(HashMap<BucketMap, K, V>, "BucketMap is not a hashmap!");
};
