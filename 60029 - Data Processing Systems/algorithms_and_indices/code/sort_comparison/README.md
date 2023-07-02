## What is this?
[Tests](tests.cpp) & [benchmarks](benchmarks.cpp) for the basic sorting algorithms discussed in the notes.

Intended as a playground to implement and compare other sorting algorithms.

## Dependencies
```
cmake 3.22
make 4.3
```

## To build & Run
```bash
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
make -j -C build/
./build/Test
./build/Benchmark
```

