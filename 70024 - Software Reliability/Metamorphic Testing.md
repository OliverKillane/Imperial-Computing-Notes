## Definition
Using transformations that semantically have no effect, to generate different programs with the same expected behaviour.
```rust
// for example if statement order
if x { A() } else { B() }
if !x { B() } else { A() }

// mathematical expressions
x = a * 3;
x = a + a + a;
```
By applying a large number of combinations of such transformations to a program, many different semantically equivalent programs can be generated.