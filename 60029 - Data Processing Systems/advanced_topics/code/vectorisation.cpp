// g++ -O3 -mavx512f vectorisation.cpp
// avx512 support is lacking, so cannot un this to test myself

#include <cstdint>
#include <cstddef>
#include <immintrin.h>
#include <type_traits>
#include <iostream>

template<size_t n>
__attribute__((noinline))
void element_sum_scalar(int64_t x[n], int64_t y[n], int64_t z[n]) {
    for (auto i = 0; i < n; i++) {
        z[i] = x[i] + y[i];
    }
}

template<size_t n>
__attribute__((noinline))
typename std::enable_if<n % 8 == 0, void>::type element_sum_vec(int64_t x[n], int64_t y[n], int64_t z[n]) { 
    for (auto i = 0; i < n; i+=8) {
        __m512i xs = _mm512_loadu_si512(&x[i]);
        __m512i ys = _mm512_loadu_si512(&y[i]);
        __m512i zs = _mm512_add_epi64(xs, ys);
        _mm512_storeu_si512(&z[i], zs);
    }
}

template<size_t n>
void randomarray(int64_t arr[n]) {
    for (auto i = 0; i < n; i++) arr[i] = std::rand();
}

template<size_t n>
void demo() {
    int64_t x[n];
    int64_t y[n];
    int64_t z[n];

    randomarray<n>(x); randomarray<n>(y);

    element_sum_vec<n>(x, y, z);

    for (auto e : z) std::cout << e << ", ";
}

int main() {
    demo<2048>();
}
