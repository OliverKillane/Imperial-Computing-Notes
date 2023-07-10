#include "hasher.h"
#include "hashtable.h"

#include "hashtables/bucket.h"
#include "hashtables/std_unordered_map.h"

#include "utils.h"

#include <iostream>
#include <functional>

using namespace std;

// :( cannot have template-template non-type params
template<typename K, Hasher<K> hash>
void hash_example() {

}

template<template<typename K, typename V> class Table>
void basic_example() {
    Table<int, int> m;
    static_assert(HashMap<decltype(m), int, int>, "not a hashmap");
    cout << "example with " << type<decltype(m)>() << endl;
    cout << "inserting (3,3): " << m.insert(3,3) << endl;
    cout << "contains 3? " << m.contains(3) << endl;
    cout << m << endl;
    cout << "erasing 3: " << m.erase(3) << endl;
    cout << "contains 3? " << m.contains(3) << endl;
    cout << m << endl;
}

template<typename K, typename V>
using BucketSTDHash = BucketMap<K, V, collision_hash<K>>;

int main() {
    basic_example<STLUnorderedMap>();
    basic_example<BucketSTDHash>();
}
