

example:   
    mov DWORD PTR [rsp-4], 1
    mov eax, 4
    mov edx, 3
    lock cmpxchg DWORD PTR [rsp-4], edx
    ret
