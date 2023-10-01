## What is this?
[Streams](streams.h) for a basic push operator playground.
- Pushes events from operator to operator
- Operators take successors references and push

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
- Tests and benchmark window aggregation implementations
