while true:
    if PC >=  length P:
        HALT!

    N = P[PC]

    if N == 0:
        HALT!

    (curr, next) = decode(N)
    C = curr
    N = next

    # either C = 2i (R+) or C = 2i + 1 (R-)
    R = A[C // 2]

    # Execute C on data R, get next label and write back to registers
    (PC, R_new) = Execute(C, R)
    A[C//2] = R_new