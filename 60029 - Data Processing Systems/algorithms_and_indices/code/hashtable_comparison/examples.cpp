#include "hasher.h"
#include "hashtable.h"
#include "utils.h"

#include "hashtables/bucket.h"
#include "hashtables/std_unordered_map.h"
#include "hashtables/probing.h"

#include "hashers/const_hash.h"
#include "hashers/std_hash.h"

#include <iostream>
#include <functional>


// :( cannot have template-template non-type params
void hash_examples() {
    std::string this_str = "The hash of this string is: ";
    std::cout << "std::hash/Hash::STD(\"" << this_str << "\") = " << Hash::STD(this_str) << std::endl;   
    std::cout << "Hash::Const(\"" << this_str << "\") = " << Hash::Const(this_str) << std::endl;
}

template<template<typename K, typename V> class Table>
void basic_example() {
    Table<int, int> m;
    static_assert(IsHashMap<decltype(m), int, int>, "not a hashmap");
    std::cout << "example with " << type<decltype(m)>() << std::endl;
    std::cout << "inserting (3,3): " << m.insert(3,3) << std::endl;
    std::cout << "contains 3? " << m.contains(3) << std::endl;
    std::cout << m << std::endl;
    std::cout << "erasing 3: " << m.erase(3) << std::endl;
    std::cout << "contains 3? " << m.contains(3) << std::endl;
    std::cout << m << std::endl;
}

template<typename K, typename V>
using BucketSTDHash = HashMap::Buckets<K, V, Hash::STD<K>>;

template<typename K, typename V>
using BucketCollisionHash = HashMap::Buckets<K, V, Hash::Const<K>>;

template<typename K, typename V>
using LinearOpenAddressing = HashMap::Probing<K, V, HashMap::Probes::Linear<K, Hash::STD<K>>>;

int main() {
    hash_examples();
    // basic_example<HashMap::STD>();
    // basic_example<BucketCollisionHash>();
    // basic_example<BucketSTDHash>();
    basic_example<LinearOpenAddressing>();
}
