## Definition
A type of [[Symbolic Execution 1]],  that obtains a set of test cases that hit all possible branches in a program.
1. Start with concrete input.
2. run it, and collect path conditions.
3. choose a given path condition, and negate it.
4. solve the new path conditions to get a new concrete input to try.
5. repeat with the new concrete input, and record that input as a test case for the user.
It is a type of [[White-Box Fuzzing]].