## What is this?
In order to understand the cost of volcano operators, we need to understand the cost of a function call.
- C++ semi-obscures this to provide better abstraction for the programmer, see an explanation in [lambda.cpp](./lambdas.cpp)
- Combined with compiler optimisation (or not) this can get a bit confusing.

## Key Takeaways
### Static/Known at Compile Time
*Not referring to the static keyword, why is the same word used for so much?!* 

The compiler knows the exact function called when it compiles the program.

For example, we can take the following code:
```cpp
// static keyword means 'cannot link this, not exposed outside of this compilation unit' in this context
static void nothing() {}

int main() {
    nothing();
}
```
You can compile this and produce assembly (e.g `g++ code.cpp -S -o code.s`)

With no optimisations we get:
```assembly
nothing():
        push    rbp
        mov     rbp, rsp
        
        nop

        pop     rbp
        ret
main:
        push    rbp
        mov     rbp, rsp
        
        # 1. push return address to stack
        # 2. EIP (x86's program counter) += immediate value 
        call    nothing()

        mov     eax, 0
        pop     rbp
        ret
```
Note: this call is a relative jump, intel x86 syntax has [several call types](https://stackoverflow.com/a/20264904).

As the compiler knows 'nothing' is being called, it can inline and optimise to:
```assembly
main:
        xor     eax, eax   # cheap way of clearing eax (return exit code 0)
        ret
```

In C++ we can express this in 3 ways:
1. Just writing normal functions, as in the example above
2. Using `auto ... = []() ... {}` lambdas. Each lambda has its own type (identifying the actual function), we cannot write this in C++ syntax, so we let the compiler deduce it using `auto`
3. *Sneakily* some function pointers (see dynamic below) can be eliminated by constant propagation. 

### Dynamic/Known at Runtime
To dynamically determine which function to call. Use pointers.
- Technically its not the only way (if you know every possible function that could be passed at compile time).

You will be familiar with the `r_type (*name)(param_type, ...)` function pointers from C.

```cpp
static void nothing() {}

static void apply(void fn(void)) { fn(); }

int main() {
    apply(nothing);
}
```
When compiling without optimisations, we get:
```assembly
nothing():
        push    rbp
        mov     rbp, rsp
        nop
        pop     rbp
        ret
apply(void (*)()):
        # equivalent to `enter`, create new stack frame
        push    rbp      
        mov     rbp, rsp 
        sub     rsp, 16  

        # 
        mov     QWORD PTR [rbp-8], rdi
        mov     rax, QWORD PTR [rbp-8]
        call    rax
        nop

        leave # destroy stack frame
        
        ret
main:
        push    rbp
        mov     rbp, rsp
        mov     edi, OFFSET FLAT:nothing()  # set arg as nothing
        call    apply(void (*)())           # call apply(nothing)
        mov     eax, 0
        pop     rbp
        ret
```

Note that as apply is `static` (not accessible out of the compilation unit / no external linkage), if we add `-O3` optimisation, constant propagation can remove the use of pointers. We cannot do this in a database system (there are an infinite number of combinations of operators in SQL).

```assembly
main:
        xor     eax, eax
        ret
```

C++ adds `std::function` and `virtual` methods on top of this, but they are both effectively implemented by function pointers.

Methods of a C++ class/struct marked virtual are called using the class's associated vtable.

<table>
<tr>
<th>Cpp</th>
<th>C</th>
</tr>
<tr>
<td>

```cpp
class Foo {
  public:
    int a;
    virtual bool which() { return false; }
    virtual int mult(int x) { return x * 3; }
};






class Bar : public Foo {
  public:
    bool b;
    int mult(int x) override {
        if (b) return x * 7; else return x;
    }
};





```

</td>
<td>

```cpp
bool Foo_which(Foo* self)        { return false; }
int  Foo_mult (Foo* self, int x) { return x * 3; }

const void* Foo_vtable[2] = {
    (void*)Foo_which,
    (void*)Foo_mult
};

struct Foo {
    const void* (*vtable)[2] = &Foo_vtable;
    int a;
};


int Bar_mult(Bar* self, int x) { if (self->b) return x * 7; else return x; }

const void* Bar_vtable[2] = {
    (void*)Foo_which,
    (void*)Bar_mult
};

struct Bar {
    const void* (*vtable)[2] = &Bar_vtable;
    int a;
    bool b;
};
```

</td>
</tr>
</table>

*Note: The C example is not compilable due to lack of forward declarations for Foo, Bar, and Bar::b*

*Note: This example is simplified, for example we do not include a pointer to the parent class's vtable*

`std::function` uses function pointers, and adds functionality to support captures. 

## Dependencies
```
cmake 3.22
make 4.3
```

## To build & Run
```bash
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
make -j -C build/
./build/Benchmark
./build/Lambdas
```

## Benchmark Results

|Benchmark                  |         Time|            CPU|  Iterations|
|---------------------------|-------------|---------------|------------|
|benchmark_nothing_fun/8192 |     0.000 ns|       0.000 ns|  1000000000|
|benchmark_nothing_fun/32768|     0.000 ns|       0.000 ns|  1000000000|
|benchmark_nothing_fun/65536|     0.000 ns|       0.000 ns|  1000000000|
|benchmark_nothing_lda/8192 |     0.000 ns|       0.000 ns|  1000000000|
|benchmark_nothing_lda/32768|     0.000 ns|       0.000 ns|  1000000000|
|benchmark_nothing_lda/65536|     0.000 ns|       0.000 ns|  1000000000|
|benchmark_nothing_ptr/8192 |      9984 ns|        9984 ns|       72477|
|benchmark_nothing_ptr/32768|     40312 ns|       40312 ns|       17206|
|benchmark_nothing_ptr/65536|     79034 ns|       79034 ns|        8490|
|benchmark_nothing_std/8192 |      8051 ns|        8051 ns|       80767|
|benchmark_nothing_std/32768|     32174 ns|       32174 ns|       22296|
|benchmark_nothing_std/65536|     63379 ns|       63378 ns|       10907|

- Function gets inlined, its `nop` so effectively no code.
- Lambda is same as function, compiler inlines so no call.
- `std::function` and function pointers require an indirect call. 
- GCC is doing something with std::function that it is not with function pointers, go investigate! (I don't know what)
