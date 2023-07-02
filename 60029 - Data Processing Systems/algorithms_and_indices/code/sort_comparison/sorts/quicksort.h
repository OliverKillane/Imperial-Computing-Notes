#pragma once
#include <vector>

using namespace std;

template <typename T, bool comp(const T&, const T&)>
size_t partition(vector<T>& sort_vec, size_t start, size_t end) {
    // select pivot
    T pivot = sort_vec[start];
    
    // find number of items before pivot ()
    size_t count = 0;
    for(size_t i = start + 1; i < end; i++) {
        if (comp(sort_vec[i], pivot)) count++;
    }

    // move pivot to its final position
    size_t pivotIndex = start + count;
    swap(sort_vec[pivotIndex], sort_vec[start]);
    size_t i = start, j = end - 1;

    // partition by finding pairs of elements that can be swapped around the pivot
    while(i < pivotIndex && j > pivotIndex) {
        while(comp(sort_vec[i], pivot)) i++;
        while(!comp(sort_vec[j], pivot)) j--;

        if(i < pivotIndex && j >= pivotIndex) {
            swap(sort_vec[i], sort_vec[j]);
            i++;
            j--;
        }
    }

    return pivotIndex;
}

template <typename T, bool comp(const T&,const T&)>
void quicksort_helper(vector<T>& sort_vec, size_t start, size_t end) {
    if(start + 1 >= end) return;

    size_t p = partition<T, comp>(sort_vec, start, end);
    quicksort_helper<T, comp>(sort_vec, start, p);
    quicksort_helper<T, comp>(sort_vec, p + 1, end);
}

template <typename T, bool comp(const T&,const T&)> void quicksort(vector<T>& sort_vec) {
    quicksort_helper<T, comp>(sort_vec, 0, sort_vec.size());
}
