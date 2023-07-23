#pragma once

#include <concepts>
#include <utility>
#include <cstddef>

// We use a concept to express a HashMap
// - we do not want runtime polymorphism (abstract class with pure virtuals)
// - we want to be able to check template parameters are a hashmap
template <typename T, typename K, typename V>
concept HashMap = requires(T& t, const T& tc) {
    { t.insert(std::declval<K>(), std::declval<V>()) } -> std::same_as<bool>;
    { t.erase(std::declval<const K&>()) } noexcept -> std::same_as<bool>;
    { t.find(std::declval<const K&>()) } noexcept -> std::same_as<V*>;
    { tc.contains(std::declval<const K&>()) } noexcept  -> std::same_as<bool>;
    { tc.size() } noexcept  -> std::same_as<size_t>;
};

template<typename K, typename V>
struct EmptyMap {
    bool insert(K, V) { return false;}
    V* find(const K&) noexcept { return nullptr; }
    bool contains(const K&) const noexcept { return false; }
    bool erase(const K&) noexcept { return false; }
    size_t size() const noexcept { return 0; }
    static_assert(HashMap<EmptyMap<K, V>, K, V>, "not a hashmap");
};

