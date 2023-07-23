
# TODO
## What is this?
[Tests](tests.cpp) & [benchmarks](benchmarks.cpp) for the basic join algorithms discussed in the notes.

Intended as a playground to implement and compare other join algorithms.

## I can do better!
The provided implementations are optimised for simplicity & readability for use in the notes pdf.
- The hashtable interface is simple, we could make it nicer (e.g take universal refs for `.insert`, throw or return reference version of find etc)
- You can go faster! submit a PR and claim victory.


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

