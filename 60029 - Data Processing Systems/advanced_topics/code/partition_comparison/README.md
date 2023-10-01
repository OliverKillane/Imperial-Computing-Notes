## What is this?
[Tests](tests.cpp) & [benchmarks](benchmarks.cpp) for the partition algorithms discussed in the advanced topics lecture.

## To build & Run
```bash
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
make -j -C build/
./build/Test
./build/Benchmark
./build/Examples
```
