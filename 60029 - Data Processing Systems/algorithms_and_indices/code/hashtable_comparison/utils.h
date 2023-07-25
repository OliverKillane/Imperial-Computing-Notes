#pragma once
#include <source_location>
#include <string>

// Helpers for getting the name of a C++ type
template <typename T>
consteval auto t_location() { return std::source_location::current().function_name(); }

template<typename T>
std::string type() {
    constexpr auto prefix_len = std::char_traits<char>::length("consteval auto t_location() [with T = ");
    std::string s(t_location<T>());
    return std::string(&s[prefix_len], &s[s.size()-1]);
}