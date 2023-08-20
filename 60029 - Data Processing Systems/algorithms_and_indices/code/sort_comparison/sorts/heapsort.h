#pragma once
#include <vector>

using namespace std;

// INV: we have a heap from heap[root+1:]
template<typename T, bool comp(const T&,const T&)>
void siftDown(vector<T>& heap, size_t root, size_t end) {
    for (;;) {
        size_t largest = root;
        size_t left_root = 2 * root + 1;
        size_t right_root = 2 * root + 2;

        if (left_root < end && comp(heap[largest], heap[left_root]))
            largest = left_root;

        if (right_root < end && comp(heap[largest], heap[right_root]))
            largest = right_root;
        
        if (largest != root) {
            swap(heap[largest], heap[root]);
            root = largest;
        } else {
            break;
        }
    }
}


template<typename T, bool comp(const T&,const T&)>
void heapsort(vector<T>& unsorted) {
    // Create a heap structure (parent is larger than both children)
    for (size_t i = unsorted.size(); i > 0; i--) {
        siftDown<T, comp>(unsorted, i - 1, unsorted.size());
    }

    // Take each element, and re-siftDown the heap
    // - unsorted[0:i] is a heap
    // - unsorted[i:] is sorted
    for (size_t i = unsorted.size(); i > 1; i--) {
        swap(unsorted[0], unsorted[i - 1]);
        siftDown<T, comp>(unsorted, 0, i - 1);
    }
}
