## What is this?
[Operators](operators.h) for a basic volcano operator implementation.
- Uses templates for output types (for simplicity), an actual system would need to return variants.
- Tests and benchmarks currently empty.

## To build & Run
```bash
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
make -j -C build/
./build/Test
./build/Benchmark
./build/Examples
```

## Contribute!
- Adding new operators.
- Pretty printing the volcano operator structure / algebra from the operators themselves.
- Counting function calls (consider our use of templates here/inlining)
