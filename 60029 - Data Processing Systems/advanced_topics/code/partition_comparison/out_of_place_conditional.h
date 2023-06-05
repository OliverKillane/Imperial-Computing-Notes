#pragma once
#include <concepts>
#include <vector>

namespace out_of_place_cond {
template<std::copy_constructible T>
size_t partition(const std::vector<T>& input_vec, std::vector<T>& output_vec, size_t start, size_t end)
{
    const T& pivot = input_vec[(start + end) / 2];  
    size_t left_index = start;
    size_t right_index = end - 1;

    for (auto i = start; i < end; i++) {
        if (input_vec[i] < pivot) {
            output_vec[left_index] = input_vec[i];
            left_index++;
        } else {
            output_vec[right_index] = input_vec[i];
            right_index--;
        }
    }

    return right_index;
}
}