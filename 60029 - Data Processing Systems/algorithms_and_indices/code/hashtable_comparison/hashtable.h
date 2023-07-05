#include <concepts>
#include <utility>

// We use a concept to express a HashMap
// - we do not want runtime polymorphism (abstract class with pure virtuals)
// - we want to be able to check template parameters are a hashmap
template <typename T, typename K, typename V>
concept HashMap = requires(T& t, const T& tc, K&& k, V&& v) {
    { t.insert(std::forward<K>(k), std::forward<V>(v)) } -> std::same_as<bool>;
    { t.erase(std::declval<const K&>()) } noexcept -> std::same_as<bool>;
    { t.find(std::declval<const K&>()) } noexcept -> std::same_as<V*>;
    { tc.contains(std::declval<const K&>()) } noexcept  -> std::same_as<bool>;
};

struct EmptyMap {
    bool insert(int&&, char&&) { return false;}
    char* find(const int&) noexcept { return nullptr; }
    bool contains(const int&) const noexcept { return false; }
    bool erase(const int&) noexcept { return false; }
};

static_assert(EmptyMap<MyMap, int, char>, "not a hashmap");