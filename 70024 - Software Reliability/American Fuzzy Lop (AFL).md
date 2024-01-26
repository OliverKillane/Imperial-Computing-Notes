## Definition
A [[Mutation-Based Fuzzer|mutation-based]], [[Dumb Fuzzing|dumb]], [[Grey-Box Fuzzing|grey-box]] fuzzer.
- General purpose and does not know input format
```python
files = get_user_provided_files()
prev_behaviour = {}
while keep_fuzzing():
	next = files.pop()
	
	# AFL measures branch coverage
	behaviour = fuzz_with(next)
	prev_benhaviour.add(behaviour)

	# trim the test case to the smallest size with the 
	# same behaviour as the original
	fuzz_and_trim(behaviour, next)

    # Mutate the file using a variety of traditional methods
	new_files = mutate(next)
	
	# If any have different behaviour, add to queue
	for mutated in new_files:
		if fuzz_with(mutated) not in prev_behaviour:
			files.append(mutated)
```

The mutation strategies used are:

| Strategy | Description |
| ---- | ---- |
| Walking Bit-Flips | Walk input with 1-bit stride, flipping 1-4 consecutive bits |
| Walking byte-flips | walk input with 1-byte stride, flipping 8, 16 or 32 consecutive bits |
| Increment/Decrement | Changed integer values in the input file (by default in range -34 to 35) |
| Insert known integers | -1, 256, 1024, MAX_INT-1 |
| Miscellaneous Random Tweaks | deleting or mem-setting parts of the input file |
| Splicing | Concatenate parts of existing input |
## [Github Repository](https://github.com/google/AFL)
## [Creator's Website](https://lcamtuf.coredump.cx/afl/)
