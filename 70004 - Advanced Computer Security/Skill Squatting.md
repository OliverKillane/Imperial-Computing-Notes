## Description
A type of [[Voice Assistant Exploit]]. Addon apps for voice assistants such as Alexa are *skills*, by making skills likely to be activated accidentally by Alexa misinterpreting speech they can be activated in place of the intended app.
- Voice equivalent of typo squatting
- Predictable errors caused by homophones, and phonetic confusion (e.g. wet/what, rip/rap, been/bean)
- Longest string match resulting in commands being shadowed

It is also possible to squat on common exit commands:
- For Alexa only *exit* is caught by the OS to exit the skill, *stop* and *cancel* are captured by the skill
## Defences
### Competitive Invocation Names
Identify suspicious variations of invocation names to detect potential squatting.
- Convert names to pronunciations (e.g. using the CMU Pronouncing Dictionary) and then get the edit-distance.
### Runtime Analysis
Detect the skill providing responses that are like the system's (e.g. pretending to have exited an application).
- Can use fuzzy matching (e.g. through encoding sentence semantics using a neural network), to quickly detect similarity
