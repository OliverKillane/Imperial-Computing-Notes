// g++ -O3 -mavx512f vectorisation.cpp
// avx512 support is lacking, so cannot un this to test myself

#include <cstdint>
#include <cstddef>
#include <immintrin.h>
#include <type_traits>
#include <iostream>

template<size_t n>
void element_sum_scalar(int64_t x[n], int64_t y[n], int64_t z[n]) {
    for (auto i = 0; i < n; i++) {
        z[i] = x[i] + y[i];
    }
}

template<size_t n>
typename std::enable_if<n % 8 == 0, void>::type element_sum_vec(int64_t x[n], int64_t y[n], int64_t z[n]) { 
    const size_t vs = n / 8;
    
    __m512i* x_vecs = reinterpret_cast<__m512i*>(x);
    __m512i* y_vecs = reinterpret_cast<__m512i*>(y);
    __m512i* z_vecs = reinterpret_cast<__m512i*>(z);

    for (auto i = 0; i < vs; i++) {
        z_vecs[i] = _mm512_add_epi64(x_vecs[i], y_vecs[i]);
    }
}

int main() {
    int64_t x[2048] = {0};
    int64_t y[2048] = {0};
    int64_t z[2048] = {0};

    element_sum_vec<2048>(x, y, z);

    for (auto e : z) std::cout << e << ", ";
}
