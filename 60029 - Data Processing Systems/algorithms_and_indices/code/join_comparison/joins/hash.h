#pragma once

#include "../table.h"
#include <unordered_map>

using namespace std;

template <size_t leftCol, size_t rightCol, typename... leftTypes, typename... rightTypes>
Table<leftTypes..., rightTypes...>
hash_join(const Table<leftTypes...> &left, const Table<rightTypes...> &right) {
    using leftColType = typename tuple_element<leftCol, tuple<leftTypes...>>::type;

    auto result = join_empty<leftCol, rightCol>(left, right);

    unordered_multimap<leftColType, const tuple<leftTypes...> *> leftContents;
    leftContents.reserve(left.rows.size());

    for (const auto &elem : left.rows) {
        leftContents.insert(make_pair(get<leftCol>(elem), &elem));
    }

    for (auto &rightRow : right.rows) {
        auto [start, end] = leftContents.equal_range(get<rightCol>(rightRow));
        for (auto entry = start; entry != end; entry++ ) {
            result.rows.emplace_back(tuple_cat(*(entry->second), rightRow));
        }
    }

    return result;
}