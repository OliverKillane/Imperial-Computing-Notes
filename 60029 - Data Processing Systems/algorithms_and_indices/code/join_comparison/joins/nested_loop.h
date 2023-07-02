#pragma once

#include "../table.h"


template <size_t leftCol, size_t rightCol, typename... TypesOne, typename... TypesTwo>
Table<TypesOne..., TypesTwo...> nested_loop_join(const Table<TypesOne...> &left, const Table<TypesTwo...> &right) {
    auto result = join_empty<leftCol, rightCol>(left, right);
    
    for (const auto &leftElem : left.rows) {
        for (const auto &rightElem : right.rows) {
            if (get<leftCol>(leftElem) == get<rightCol>(rightElem)) {
                result.rows.emplace_back(tuple_cat(leftElem, rightElem));
            }
        }
    }

    return result;
}