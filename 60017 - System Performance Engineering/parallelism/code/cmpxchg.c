#include <stdatomic.h>

void example() {
    int a = 1;
    int b = 4;
    int temp = 3;
    atomic_compare_exchange_strong(&a, &b, temp);
    return;
}
