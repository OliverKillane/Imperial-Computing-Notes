#include <stdint.h>
#include <stddef.h>

extern int32_t* input_data_1; // uniform random data (used for index)
extern int32_t* input_data_2; // random data
extern size_t N;              // A large constant

void benchmark() {
    int32_t sum = 0;
    for (size_t i = 0; i < N; i++)
        sum += input_data_2[input_data_1[i]];
}
