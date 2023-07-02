#pragma once
#include <vector>

using namespace std;
 
vector<int> ordered_ints(size_t n) {
    vector<int> vec;
    vec.reserve(n);
    for (auto i = 0; i < n; i++) vec.push_back(i);
    return vec;
}

vector<int> reverse_ordered_ints(size_t n) {
    vector<int> vec;
    vec.reserve(n);
    for (auto i = n; i > 0; i--) vec.push_back(i);
    return vec;
}

vector<int> alternating_ints(size_t n) {
    vector<int> vec;
    vec.reserve(n);
    for (auto i = 0; i < n; i++) vec.push_back(i % 2 == 0 ? i : n - i);
    return vec;
}

vector<int> random_ints(size_t n) {
    vector<int> vec;
    vec.reserve(n);
    srand(n);
    for (auto i = 0; i < n; i++) vec.push_back(rand());
    return vec;
}