## Definition
A [[Fuzzing|fuzzer]]'s input generator can observe the behaviour of the [[SUT]] to inform new inputs.
- Currently the state of the art for fuzzing.

*Interesting inputs can*
- Log a previously unseen message
- Cover some previously uncovered code
- Consume more memory than usual
- Do some previously unseen IO (e.g. system call)

| Fuzzing | To Take Advantage |
| ---- | ---- |
| [[Generation-Based Fuzzer]] | Attempt to generate inputs with similar properties. |
| [[Mutation-Based Fuzzer]] | Prioritise the used templates as candidates for the next inputs. |
