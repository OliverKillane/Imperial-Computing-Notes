---- MODULE test ----
EXTENDS TLC

[A]_v, [A]_<<v1,v2,v3>>
<<A>>_v, <A>_<<v1,v2,v3>>
ENABLED A

[]F
<>F
F1 ~> F2
WF_v(A), SF_v(A)
====