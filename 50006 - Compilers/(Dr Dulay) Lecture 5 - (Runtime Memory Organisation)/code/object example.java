class MyClass {
    int x;
    int y;

    method ... p(...) {...}
    method ... q(...) {...}
}

MyClass A = new MyClass();
MyClass B = new MyClass();

B.q(...) // MyClass.q(&B, ...)