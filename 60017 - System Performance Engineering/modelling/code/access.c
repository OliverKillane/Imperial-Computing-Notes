#include <stdint.h>
#include <stddef.h>

extern int32_t* input_data; // An array of data
extern size_t N;            // A large constant
extern size_t size;         // Parameter: size of the region accessed

void benchmark() {
    volatile int32_t sum = 0;
    for (size_t i = 0; i < N; i++)
        // mod is used (expensive), to reduce use size power of 2 and a bitmask
        sum += input_data[i % size];
}
