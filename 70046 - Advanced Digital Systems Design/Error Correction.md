## Fault Sources
- Radiation (alpha particles hitting silicon and inducing enough charge to cause a bit flip)
- Hardware breakage (by manufacturing or over lifetime due to aging)
## Error Detection
### Parity Bits
Adding a single bit to a set of bits that represents the number of `1`s.
- Can detect an odd number of fault events (as this changes the parity bit)

We can include multiple check parity bits to allow error correction (to deduce which bit was flipped, given a single fault).
```rust
P0 = parity(D0, D1, D3)
P1 = parity(D0, D2, D3)
P2 = parity(D1, D2, D3)

// If only one of P0, P1, P2 is unchanged, then we can deduce which data bit was changed
```
Each data bit needs to affect a different combination of check bits to allow us to infer the data bit changed, from the check bit change.
$$2^n -n - 1 \ \text{data bits are covered by} \ n \ \text{ parity bits}$$
- $n$ bits means $2^n$ combinations
- of the $2^n$ combinations, only $n$ affect a single bit (`...010...`)
- one combination should change no bits (no parity change)
```python
def parity(bits: list[bool]) -> bool:
    """ Parity as the number of 1s is odd=True, even=False """
    return bool(sum(bits) % 2)

def gen_indexes(size: int) -> list[set[int]]:
    """ Generate the parity indexes for `size` data bits
        [index{parity indices... }, ]
        - If all parities chan ge except index, then index was flipped.
        - The set contains the bit indicies to calculate parity
    """
    return [{j for j in range(size) if j != i} for i in range(size)]

def gen_parity_bits(data_bits: list[bool]) -> list[bool]:
    """ Get the error correction bits """
    return [parity([data_bits[i] for i in s]) for s in gen_indexes(len(data_bits))]
  
def check(data_bits: list[bool], parity_bits: list[bool]) -> int | None | str:
    """ Compares the parity
    single fault => (all except one parity bit are flipped) then 
                    return the data bit index flipped
    string       => double fault
    none         => no change
    """
    same_index: int | None = None
    differing: bool = False
    for i, (o, n) in enumerate(zip(parity_bits, gen_parity_bits(data_bits))):
        if o == n:
            if same_index is not None and differing:
                return "Double fault"
            same_index = i
        else:
            differing = True
    return same_index

original_bits = [True, True, False, False, True]
original_parity = gen_parity_bits(original_bits)
new_bits = [True, False, False, False, True]
new_parity = gen_parity_bits(new_bits)
assert check(new_bits, original_parity) == 1
```

We can also add an extra bit fir the parity of the parity bits (to detect double faults)
### Basic Checksum
Add all data words together (ignoring carry) and store result.
- Easy to compute
- Errors can cancel out (no error detected)
### Modified Checksum
On every carry, add a 1 instead, this way carry information is not entirely lost.
- Errors can still cancel out
### Cyclic Redundancy Check
Use polynomial division
[[TODO]]