#include <stdio.h>
#include <stdlib.h>


int a = 6;

void pretty_print(int num) {
    printf("The number is: %d", num);
}

int another_cool_function(int* num) {
    *num++;
    return *num - 1;
}

int main(int argc, char **argv) {
    int b = 7;

    pretty_print(a + b);

    return EXIT_SUCCESS;
}