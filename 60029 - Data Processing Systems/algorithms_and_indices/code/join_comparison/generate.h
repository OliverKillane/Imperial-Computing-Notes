// helper functions for generating the tables used in the benchmarks

#include "table.h"

#include <tuple>
#include <string>
#include <source_location>

#include <iostream>

using namespace std;

// NOTE: I may have gone a bit over the top with this

template<typename... types> using Gen = tuple<types...> (size_t i);

template<size_t i, typename... Ts>
using index = typename tuple_element<i, tuple<Ts...>>::type;

// Helpers for getting the name of a C++ type
template <typename T>
consteval auto t_location() {
    const auto& loc = std::source_location::current();
    return loc.function_name();
}

template<typename T>
string type() {
    constexpr auto prefix_len = char_traits<char>::length("consteval auto t_location() [with T = ");
    string s(t_location<T>());
    return string(&s[prefix_len], &s[s.size()-1]);
}

template<size_t i, typename... Ts> void typenames(array<string, sizeof...(Ts)>& names) {
    if constexpr (i < sizeof...(Ts)) {
        names[i] = type<index<i, Ts...>>();
        typenames<i+1, Ts...>(names);
    }
}

template<typename... Ts>
struct create_table {
    template<Gen<Ts...> gen>
    static Table<Ts...> with_gen(size_t rows) {
        Table<Ts...> t{.name = "generated",};
        typenames<0, Ts...>(t.cols);
        for (size_t row = 0; row < rows; row++) {
            t.rows.push_back(gen(row));
        }
        return t;
    }
};


constexpr auto gen_ints = [](size_t i) -> auto {return make_tuple(0,0,0);};
void example_ints() {
    auto t = create_table<int, int, int>::with_gen<+gen_ints>(5);
    cout << t;
}

constexpr auto gen_mixed = [](size_t i) -> auto {return make_tuple(i, string(i, 'a'), i % 2 == 0);};
void example_mixed() {
    auto t = create_table<size_t, string, bool>::with_gen<+gen_mixed>(10);
    cout << t;
}
