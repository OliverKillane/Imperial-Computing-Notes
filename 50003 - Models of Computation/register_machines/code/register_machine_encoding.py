from typing import List, Tuple
from collections import namedtuple

# Register Instructions
Inc = namedtuple('Inc', 'reg label')
Dec = namedtuple('Dec', 'reg label1 label2')
Halt = namedtuple('Halt', '')

''' 
 __          ________ _      _____ ____  __  __ ______ 
 \ \        / /  ____| |    / ____/ __ \|  \/  |  ____|
  \ \  /\  / /| |__  | |   | |   | |  | | \  / | |__   
   \ \/  \/ / |  __| | |   | |   | |  | | |\/| |  __|  
    \  /\  /  | |____| |___| |___| |__| | |  | | |____ 
     \/  \/   |______|______\_____\____/|_|  |_|______|
                                                       
This file can be used to quickly create, run, encode & decode register machine 
programs. Furthermore it prints out the workings as formatted latex for easy 
use in documents.

Here making use of python's ints as they are arbitrary size (Rust's bigInts 
are 3rd party and awful by comparison). 

To create register Instructions simply use:
Dec(reg, label 1, label 2)
Inc(reg, label)
Halt()

To ensure your latex will compile, make sure you have commands for, these are 
available on my github (Oliver Killane) (Imperial-Computing-Year-2-Notes):

% register machine helper commands:
\newcommand{\instrlabel}[1]{\text{\textcolor{teal}{$L_{#1}$}}}
\newcommand{\reglabel}[1]{\text{\textcolor{orange}{$R_{#1}$}}}
\newcommand{\instr}[2]{\instrlabel{#1} : & $#2$ \\}
\newcommand{\dec}[3]{\reglabel{#1}^- \to \instrlabel{#2}, \instrlabel{#3}}
\newcommand{\inc}[2]{\reglabel{#1}^+ \to \instrlabel{#2}}
\newcommand{\halt}{\text{\textcolor{red}{\textbf{HALT}}}}

To see examples, go to the end of this file.
'''

# for encoding numbers as <a,b>
def encode_large(x: int, y: int) -> int:
    return (2 ** x) * (2 * y+1)

# for decoding n -> <a,b>
def decode_large(n: int) -> Tuple[int, int]:
    x = 0;
    
    # get zeros from LSB
    while (n % 2 == 0 and n != 0):
        x += 1
        n /= 2
    y = int((n - 1) // 2)
    return (x,y)

# for encoding <<a,b>> -> n
def encode_small(a: int, b: int) -> int:
    return encode_large(a,b) - 1

# for decoding n -> <<a,b>>
def decode_small(n: int) -> Tuple[int, int]:
    return decode_large(n+1)

# for encoding [a0,a1,a2,...,an] -> <<a0, <<a1, <<a2, <<... <<an, 0 >>...>> >> >> >> -> n
def encode_large_list(lst: List[int]) -> int:
    return encode_large_list_helper(lst, 0)[0]

def encode_large_list_helper(lst: List[int], step: int) -> Tuple[int, int]:
    buffer = r"\to" * step
    if (step == 0):
        print(r"\begin{center}\begin{tabular}{r l l}")
    if len(lst) == 0:
        print(f"{step} &" + rf"$ {buffer} 0$ & (No more numbers in the list, can unwrap recursion) \\")
        return (0, step)
    else:

        print(rf"{step} & $ {buffer} \langle \langle {lst[0]}, \ulcorner {lst[1:]} \urcorner \rangle \rangle $ & (Take next element {lst[0]}, and encode the rest {lst[1:]}) \\")
        
        (b, step2) = encode_large_list_helper(lst[1:], step + 1)
        c = encode_large(lst[0], b)
        
        step2 += 1

        print(f"{step2} & $ {buffer} \langle \langle {lst[0]}, {b} \\rangle \\rangle = {c} $ & (Can now encode) \\\\")

        if (step == 0):
            print(r"\end{tabular}\end{center}")
        return (encode_large(lst[0], b), step2)

# decode a list from an integer
def decode_large_list(n : int) -> List[int]:
    return decode_large_list_helper(n, [], 0)

def decode_large_list_helper(n : int, prev : List[int], step : int = 0) -> List[int]:
    if (step == 0):
        print(r"\begin{center}\begin{tabular}{r l l l}")
    if n == 0:
        print(rf"{step} & $0$ & ${prev}$ & (At the list end) \\")
        return prev
    else:
        (a,b) = decode_large(n)
        prev.append(a)
        print(rf"{step} & ${n} = \langle \langle {a}, {b} \rangle \rangle \ \ $&$ {prev}$ & (Decode into two integers) \\ ")

        next = decode_large_list_helper(b, prev, step + 1)

        if (step == 0):
            print(r"\end{tabular}\end{center}")
        
        return next

# For encoding register machine instructions
# R+(i) -> L(j)
def encode_inc(instr: Inc) -> int:
    encode = encode_large(2 * instr.reg, instr.label)
    print(rf"$\ulcorner \inc{{{instr.reg}}}{{{instr.label}}} \urcorner = \langle \langle 2 \times {instr.reg}, {instr.label} \rangle \rangle = {encode}$")
    return encode

# R-(i) -> L(j), L(k)
def encode_dec(instr: Dec) -> int:
    encode: int =  encode_large(2 * instr.reg + 1, encode_small(instr.label1 ,instr.label2))
    print(rf"$\ulcorner \dec {{{instr.reg}}}{{{instr.label1}}}{{{instr.label2}}} \urcorner = \langle \langle 2 \times {instr.reg} + 1, \langle {instr.label1}, {instr.label2} \rangle \rangle \rangle = {encode}$")
    return encode

# Halt
def encode_halt() -> int:
    print(rf"$\ulcorner \halt \urcorner = 0 $")
    return 0

# encode an instruction
def encode_instr(instr) -> int:
    if type(instr) == Inc:
        return encode_inc(instr)
    elif type(instr) == Dec:
        return encode_dec(instr)
    else:
        return encode_halt()

# display register machine instruction in latex format
def instr_to_str(instr) -> str:
    if type(instr) == Inc:
        return rf"\inc{{{instr.reg}}}{{{instr.label}}}"
    elif type(instr) == Dec:
        return rf"\dec{{{instr.reg}}}{{{instr.label1}}}{{{instr.label2}}}"
    else:
        return r"\halt"

# decode an instruction
def decode_instr(x: int) -> int:
    if x == 0:
        return Halt()
    else:
        assert(x > 0)
        (y,z) = decode_large(x)
        if (y % 2 == 0):
            return Inc(int(y / 2), z)
        else:
            (j,k) = decode_small(z)
            return Dec(y // 2, j, k)

# encode a program to a number by encoding instructions, then list
def encode_program_to_list(prog : List) -> List[int]:
    encoded = []
    print(r"\begin{center}\begin{tabular}{r l l}")
    for (step, instr) in enumerate(prog):
        print(f"{step} & ")
        encoded.append(encode_instr(instr))
        print(r"& \\")
    print(r"\end{tabular}\end{center}")
    print(f"\[{encoded}\]")
    return encoded

# encode a program as an integer
def encode_program_to_int(prog: List) -> int:
    return encode_large_list(encode_program_to_list(prog))

# decode a program by decoding to a list, then decoding each instruction
def decode_program(n : int):
    decoded = decode_large_list(n)
    prog = []
    prog_str = []
    for num in decoded:
        instr = decode_instr(num)
        prog_str.append(instr_to_str(instr))
        prog.append(instr)
    print(f"\[ [ {', '.join(prog_str)} ] \]")
    return prog

# print program in latex form
def program_str(prog) -> str:
    prog_str = []
    for (num, instr) in enumerate(prog):
        prog_str.append(rf"\instr{{{num}}}{{{instr_to_str(instr)}}}")
    print(r"\begin{center}\begin{tabular}{l l}")
    print("\n".join(prog_str))
    print(r"\end{tabular}\end{center}")

# run a register machine with an input:
def program_run(prog, instr_no : int, registers : List[int])-> Tuple[int, List[int]]:
    # step instruction label R0 R1 R2 ... (info)
    print(rf"\begin{{center}}\begin{{tabular}}{{l l l c" + " c" * len(registers) + " }")
    print(r"\textbf{Step} & \textbf{Instruction} & \instrlabel{{i}} &" + " & ".join([rf"$\reglabel{{{n}}}$" for n in range(0, len(registers))]) + r" & \textbf{Description}\\")
    print(r"\hline")
    step = 0
    while True:
        step_str = rf"{step} & ${instr_to_str(prog[instr_no])}$ & ${instr_no}$ & " + "&".join([f"${n}$" for n in registers]) + "&"
        instr = prog[instr_no]
        if type(instr) == Inc:
            if (instr.reg >= len(registers)):
                print(step_str + rf"(register {instr.reg} is does not exist)\\")
                break
            elif instr.label >= len(prog):
                print(step_str + rf"(label {instr.label} is does not exist)\\")
                break
            else:
                registers[instr.reg] += 1
                instr_no = instr.label
                print(step_str + rf"(Add 1 to register {instr.reg} and jump to instruction {instr.label})\\")
        elif type(instr) == Dec:
            if (instr.reg >= len(registers)):
                print(step_str + rf"(register {instr.reg} is does not exist)\\")
                break
            elif registers[instr.reg] > 0:
                if instr.label1 >= len(prog):
                    print(step_str + rf"(label {instr.label1} is does not exist)\\")
                    break
                else:
                    registers[instr.reg] -= 1
                    instr_no = instr.label1
                    print(step_str + rf"(Subtract 1 from register {instr.reg} and jump to instruction {instr.label1})\\")
            else:
                if instr.label2 >= len(prog):
                    print(step_str + rf"(label {instr.label2} is does not exist)\\")
                    break
                else:
                    instr_no = instr.label2
                    print(step_str + rf"(Register {instr.reg} is zero, jump to instruction {instr.label2})\\")
        else:
            print(step_str + rf"(Halt!)\\")
            break
        step += 1
    print(r"\end{tabular}\end{center}")
    print("\[(" + ", ".join([str(instr_no)] + list(map(str, registers))) + ")\]")
    return (instr_no, registers)

# Basic tests for program decode and encode
def test():
    prog_a = [
        Dec(1,2,1),
        Halt(),
        Dec(1,3,4),
        Dec(1,5,4),
        Halt(),
        Inc(0,0)]

    prog_b = [
        Dec(1,1,1),
        Halt()
    ]

    # set R0 to 2n for n+3 instructions
    prog_c = [
        Inc(1,1),
        Inc(0,2),
        Inc(0,3),
        Inc(0,4),
        Inc(0,5),
        Inc(0,6),
        Inc(0,7),
        Dec(1, 0, 9),
        Halt()
    ]

    assert decode_program(encode_program_to_int(prog_a)) == prog_a
    assert decode_program(encode_program_to_int(prog_b)) == prog_b
    assert decode_program(encode_program_to_int(prog_c)) == prog_c

# Examples usage
def examples():
    program_run([
        Dec(1,2,1),
        Halt(),
        Dec(1,3,4),
        Dec(1,5,4),
        Halt(),
        Inc(0,0)
    ], 0, [0,7])

    encode_program_to_list([
        Inc(1,1),
        Inc(0,2),
        Inc(0,3),
        Inc(0,4),
    ])

    encode_program_to_int([
        Dec(1,2,1),
        Halt(),
        Dec(1,3,4),
        Dec(1,5,4),
        Halt(),
        Inc(0,0)
    ])

    decode_program((2 ** 46) * 20483)

# examples()
