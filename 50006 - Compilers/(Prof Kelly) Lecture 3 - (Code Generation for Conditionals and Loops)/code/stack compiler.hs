data Stat = 
    Assign Name Exp | 
    Seq Stat Stat | 
    ForLoop Name Exp Exp Stat
    deriving (Show)

data Exp = 
    BinOp Op Exp Exp | 
    Unop Op Exp | 
    Ident Name | 
    Const Int
    deriving (Show)

data Op = 
    Plus | 
    Minus | 
    Times | 
    Divide
    deriving (Show)

type Name = [Char]

data Instruction
    = Add | Sub | Mul | Div
    | PushImm Int   -- Push an immediate value
    | PushAbs Name  -- push variable at given location on the Stack
    | Pop Name      -- remove the top of the stack and store at location name
    | CompEq         -- Subtract top two elements of the stack, replace with a 
                    -- 1 is the result was zero, zero otherwise
    | Jump Label    -- Jump to the label
    | JTrue Label   -- Remove top item from stack, if 1 jump to label
    | JFalse Label  -- Remove top item from stack, if 0 jump to label
    | Define Label  -- Set destination for jump (An assembler directive, 
                    -- not instruction).

type Label = [Char]

transExp :: Exp -> [Instruction]
transExp (BinOp op e1 e2)
    = transExp e1 ++ transExp e2 ++ [case op of
        Plus -> Add
        Minus -> Sub
        Times -> Mul
        Divide -> Div]
transExp (Unop Minus e)
    = transExp e ++ [PushImm (-1), Mul]
transExp (Unop _ _)
    = error "(transExp) Only '-' unary operator supported"
transExp (Ident id) = [PushAbs id]
transExp (Const n) = [PushImm n]

transStat :: Stat -> [Instruction]
transStat (Assign id exp) = transExp exp ++ [Pop id]
transStat (Seq s1 s2) = transStat s1 ++ transStat s2


{-
for x:e1 to e2 do
    body
od

x := <e1>
loop:
    if <e2> then goto break
    <body>
    x := x + 1
    goto loop
break:


<transExp e1>
Pop x
define "loop"
<tranEval e2>
CompEq
JTrue "break"
<transStat body>
PushImm 1
Add
Pop x
Jump "loop"
Define "break"
-}

-- assumes the labels will be unique, this almost always not the case
transStat (ForLoop x e1 e2 body)
 = transExp e1 ++ Pop x:Define "loop":transExp e2 ++ CompEq:JTrue "break":transStat body ++ [PushImm 1, Add, Pop x, Jump "loop", Define "break"]