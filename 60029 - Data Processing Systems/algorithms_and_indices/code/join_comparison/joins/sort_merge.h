#pragma once

#include "../table.h"

#include <algorithm>

using namespace std;

// A sort merge join, that assumes there are no duplicates on the left table.
template <size_t leftCol, size_t rightCol, typename... leftTypes, typename... rightTypes>
Table<leftTypes..., rightTypes...> sort_merge_join(const Table<leftTypes...> &left, const Table<rightTypes...> &right) {
    auto result = join_empty<leftCol, rightCol>(left, right);

    // copy tables (so we can keep const, just reorder)
    auto left_copy = left;
    auto right_copy = right;

    sort(left_copy.rows.begin(), left_copy.rows.end(), [](auto const &a, auto const &b) {
        return get<leftCol>(a) < get<leftCol>(b);
    });
    sort(right_copy.rows.begin(), right_copy.rows.end(), [](auto const &a, auto const &b) {
        return get<rightCol>(a) < get<rightCol>(b);
    });

    auto leftIndex = 0;
    auto rightIndex = 0;

    // the index on the right, of the start of a sequence of equal values, that 
    // are equal to the current left index
    size_t last_eq_rightIndex = 0;

    while (leftIndex < left.rows.size() && rightIndex < right.rows.size()) {
        auto leftRow = left_copy.rows[leftIndex];
        auto rightRow = right_copy.rows[rightIndex];

        if (get<leftCol>(leftRow) < get<rightCol>(rightRow)) {
            // left is smaller, so advance left
            leftIndex++;
        } else if (get<leftCol>(leftRow) > get<rightCol>(rightRow)) {
            // right is smaller, so advance right
            rightIndex++;
            last_eq_rightIndex = rightIndex;
        } else {
            // join the current rows
            result.rows.emplace_back(tuple_cat(leftRow, rightRow));

            // advance right
            rightIndex++;
            auto next_leftIndex = leftIndex + 1;

            if (rightIndex < right.rows.size()) {
                auto next_rightElem = get<rightCol>(right_copy.rows[rightIndex]);

                if (get<rightCol>(rightRow) != next_rightElem && next_leftIndex < left_copy.rows.size()) {
                    // the next rightElem is larger, and the next left is in bounds

                    if (get<leftCol>(left_copy.rows[next_leftIndex]) == get<leftCol>(leftRow)) {
                        
                        //                left   right
                        //                 ...   ...
                        //                   A   C <- last_eq_rightIndex
                        //      leftIndex -> C   C 
                        // next_leftIndex -> C   C <------ rightIndex
                        //                 ...   D <- next_rightIndex
                        //                       ...
                        // Advance leftIndex 
                        // Move rightIndex back to start of Cs

                        leftIndex++;
                        rightIndex = last_eq_rightIndex;
                    } else {
                        
                        //                left   right
                        //                 ...   ...
                        //                   A   C <- last_eq_rightIndex
                        //      leftIndex -> C   C 
                        // next_leftIndex -> D   C <------ rightIndex
                        //                 ...   E <- next_rightIndex
                        // 
                        // Advance leftIndex 
                        // Set last_eq_rightIndex to next_rightIndex

                        leftIndex++;    
                        last_eq_rightIndex = rightIndex;
                    }
                } else {
                    // loop will end (rightIndex is beyond bounds of right table)
                }
            } else if (next_leftIndex < left_copy.rows.size() && get<leftCol>(left_copy.rows[next_leftIndex]) == get<leftCol>(leftRow)) {
                //                left   right
                //                   A   C <- last_eq_rightIndex
                //      leftIndex -> C   C 
                // next_leftIndex -> C   C <------ rightIndex
                //                 ...   [end of table]
                // 
                // Advance leftIndex
                // Set rightIndex to last_eq_rightIndex

                rightIndex = last_eq_rightIndex;
                leftIndex++;
            }
        }
    }

    return result;
}