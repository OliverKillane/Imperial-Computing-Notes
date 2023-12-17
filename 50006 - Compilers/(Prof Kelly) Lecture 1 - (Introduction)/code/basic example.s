test_fun:
        movl    b(%rip), %eax
        addl    $42, %eax
        movl    %eax, a(%rip)
        ret
b:
        .zero   4
a:
        .zero   4