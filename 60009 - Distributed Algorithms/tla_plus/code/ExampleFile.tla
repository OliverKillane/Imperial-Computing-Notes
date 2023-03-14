---- MODULE name ----
EXTENDS m1, ..., mN   \* extends multiple modules
CONSTANTS c1, ..., cN \* constants are defined in the .cfg file
VARIABLES v1, ..., vN
Vars == << v1, ..., vN >>
Type == v1_formula /\ ... /\ vN_formula
----------------------------------
\* Specification for state machine

Init == formula \* Initial state
Def1 == formula \* Definitions (any number of)

\* Can have any number of subactions of Next
Action1 == action_formula

\* Determine Next State
Next == Action1 \/ ... \/ ActionN
---------------------------------
Fair == fairness_formula /\ ...
Spec == Init /\ [][Next]_Vars /\ Fair
-------------------------------------
NotDeadlock == [](ENABLED Next) \* Properties
Typed = []Type
====