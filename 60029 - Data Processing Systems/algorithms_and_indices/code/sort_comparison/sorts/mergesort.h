#pragma once
#include <vector>
#include <iostream>

using namespace std;

template<typename T, bool comp(const T&,const T&)> 
vector<T> mergesort_helper(const vector<T>& unsorted, size_t start, size_t end) {
    if (end - start == 1) {
        return {unsorted[start]};
    } else {
        // determine split
        const size_t mid = (start + end) / 2;

        // recursively mergesort
        const vector<T> left_split = mergesort_helper<T, comp>(unsorted, start, mid);
        const vector<T> right_split = mergesort_helper<T, comp>(unsorted, mid, end);
        
        // merge splits
        vector<T> merged;
        merged.reserve(end - start);

        // add largest to merged vector until one split is empty
        size_t left_ptr = 0;
        size_t right_ptr = 0;
        while (left_ptr < left_split.size() && right_ptr < right_split.size()) {
            const T& left = left_split[left_ptr];
            const T& right = right_split[right_ptr];
            if (comp(left, right)) {
                merged.push_back(left);
                left_ptr++;
            } else {
                merged.push_back(right);
                right_ptr++;
            }
        }

        // add empty split to vector, here only one loop iterates
        while (right_ptr < right_split.size()) {
                merged.push_back(right_split[right_ptr]);
                right_ptr++;
        }
        while (left_ptr < left_split.size()) {
                merged.push_back(left_split[left_ptr]);
                left_ptr++;
        }

        return merged;
    }
}

template<typename T, bool comp(const T&, const T&)> void mergesort(vector<T>& unsorted) {
    if (unsorted.size() > 0) {
        vector<T> sorted = mergesort_helper<T, comp>(unsorted, 0, unsorted.size());
        swap(sorted, unsorted);
    }
}
