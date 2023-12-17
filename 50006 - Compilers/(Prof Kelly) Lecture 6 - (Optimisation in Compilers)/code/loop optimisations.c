
/* Loop invariant Code motion */
int a = 7;
for (int b = 0; b < 4; b++) {
    int c = a + 3 * 2; // invariant code
    printf("%d", c);
}

int a = 7;
int c = a + 3 * 2; // code hoisted out of loop
for (int b = 0; b < 4; b++) {
    printf("%d", c);
}

/* Strength Reduction */
int a = 7;
for (int b = 0; b < 4; b++) {
    a += 4;
    printf("added 4 to a");
}

int a = 23; // 7 + 4 * 4
for (int b = 0; b < 4; b++) {
    printf("added 4 to a");
}


int a = 9;
int b = 7;
while (some_predicate(a)) {
    b = some_function(b);
    for (int i = 0; i < b; b++) {
        a++
    }
}

int a = 9;
int b = 7;
while (some_predicate(a)) {
    b = some_function(b);
    a += b
}

/* Control Variable Selection */
int* a = malloc(15 * sizeof(int));
for (int i = 0; i < 15; i++) {
    a[i] = 5;
}

int* a = malloc(15 * sizeof(int));
int* end = a + 15;
for (; a != end; a++) {
    *a = 5;
}
