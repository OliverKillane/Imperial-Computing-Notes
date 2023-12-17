class MyClass {
    int x;
    int y;

    method ... p(...) {...}
    method ... q(...) {...}
}

class ChildClass {
    int z;

    override method ... q(...) {...}

    method ... r(...) {...}
}

MyClass A = new MyClass();
MyClass B = new ChildClass();