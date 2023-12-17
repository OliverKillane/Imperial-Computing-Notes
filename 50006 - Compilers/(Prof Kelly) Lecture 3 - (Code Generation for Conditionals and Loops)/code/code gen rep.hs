[
    Define "start",
    PushAbs "i",
    PushImm 1,
    Sub,
    Pop "i",
    PushAbs "i",
    CompEq,
    Jtrue "Start"
]