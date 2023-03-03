#include <stdlib.h>
#include <iostream>

int main() {
    int* a = (int*) malloc(100);
    a[-1] = 3;

    std::cout << "here"<< std::endl;
}