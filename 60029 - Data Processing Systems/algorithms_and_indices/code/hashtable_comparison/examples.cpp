#include "hasher.h"
#include "hashtable.h"

#include "hashtables/bucket.h"
#include "hashtables/std_unordered_map.h"

#include <iostream>
#include <source_location>
#include <functional>

using namespace std;


// Helpers for getting the name of a C++ type
template <typename T>
consteval auto t_location() { return std::source_location::current().function_name(); }

template<typename T>
string type() {
    constexpr auto prefix_len = char_traits<char>::length("consteval auto t_location() [with T = ");
    string s(t_location<T>());
    return string(&s[prefix_len], &s[s.size()-1]);
}

// :( cannot have template-template non-type params
template<typename K, Hasher hash<K>>
void hash_example() {

}

template<template<typename K, typename V> class Table>
void basic_example() {
    Table<int, int> m;
    static_assert(HashMap<decltype(m), int, int>, "not a hashmap");
    cout << "example with " << type<decltype(m)>() << endl;
    cout << "inserting (3,3): " << m.insert(3,3) << endl;
    cout << "contains 3? " << m.contains(3) << endl;
    cout << "erasing 3: " << m.erase(3) << endl;
    cout << "contains 3? " << m.contains(3) << endl;
}

template<typename K, typename V>
using BucketSTDHash = BucketMap<K, V, my_hash<K>>;

int main() {
    basic_example<STLUnorderedMap>();
    basic_example<BucketSTDHash>();
}
