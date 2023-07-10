#pragma once
#include <source_location>
#include <string>

// Helpers for getting the name of a C++ type
template <typename T>
consteval auto t_location() { return std::source_location::current().function_name(); }

template<typename T>
string type() {
    constexpr auto prefix_len = char_traits<char>::length("consteval auto t_location() [with T = ");
    string s(t_location<T>());
    return string(&s[prefix_len], &s[s.size()-1]);
}