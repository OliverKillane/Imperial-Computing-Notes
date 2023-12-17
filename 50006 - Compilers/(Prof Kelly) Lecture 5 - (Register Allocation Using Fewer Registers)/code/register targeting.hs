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
   = Add Register Register | Sub Register Register 
    | Mul Register Register | Div Register Register -- Op r1 r2 -> r1 := r1 <Op> r2
    | AddImm Register Int | SubImm Register Int 
    | MulImm Register Int | DivImm Register Int -- <Op>Imm r c -> r := r <Op> c 
    | AddStack Register | SubStack Register
    | MulStack Register | DivStack Register -- <Op>Imm r c -> r := r <Op> mem[SP]; SP--
    | Load Register Name    -- Load r1 n    -> r1 := mem[n]
    | LoadImm Register Int  -- LoadImm r1 i -> r1 := i
    | Store Register Name   -- Load r1 n    -> mem[n] := r1
    | Push Register         -- Push r1      -> SP++; mem[SP] := r1
    | Pop Register          -- Pop r2       -> r1 := mem[SP]; SP--
    | CompEq Register Register   -- CompEq r1 r2 -> r1 := r1 - r2 = 0 ? 1 : 0
    | JTrue Register Label  -- JTrue r1 l   -> IF r1 = 1 THEN JUMP TO l
    | JFalse Register Label -- JFalse r1 l  -> IF r1 = 0 THEN JUMP TO l
    | Define Label     -- Assembler directive to set up label
    deriving(Show)

transOp :: Op -> (Int -> Int -> Instruction)
transOp Plus = Add
transOp Minus = Sub
transOp Times = Mul
transOp Divide = Div

transOpImm :: Op -> (Int -> Int -> Instruction)
transOpImm Plus = AddImm
transOpImm Minus = SubImm
transOpImm Times = MulImm
transOpImm Divide = DivImm

transOpStack :: Op -> (Int -> Instruction)
transOpStack Plus = AddStack
transOpStack Minus = SubStack
transOpStack Times = MulStack
transOpStack Divide = DivStack


weight :: Exp -> Int
-- Base cases, registers required to hold values
weight (Const _) = 1
weight (Ident _) = 1

-- Can use immediate operand multiply so no extra registers required
weight (Unop Minus e) = weight e
weight (Unop _ e) = error "(weight) can only use unary operator -"

-- As we can target registers, if either is a constant we can use immediate operands
weight (BinOp Plus (Const _) e)  = weight e
weight (BinOp Times (Const _) e) = weight e
weight (BinOp _ e (Const _))     = weight e

-- Use maximum of either 
weight (BinOp _ e1 e2)
    = min e1first e2first
    where
        e1first = max (weight e1) (weight e2 + 1)
        e2first = max (weight e2) (weight e1 + 1)

type Register = Int
type Label = [Char]

transExp :: Exp -> [Register] -> [Instruction]
transExp (Const n) (dest:rest) = [LoadImm dest n]
transExp (Ident x) (dest:rest) = [Load dest x]

-- Get result into dest register, the negate
transExp (Unop Minus e) reg@(dest:_) = transExp e reg ++ [MulImm dest (-1)]
transExp (Unop _ _) _
  = error "(transExp) Only '-' unary operator supported"

-- If the constant is on the right, we can use all operations
transExp (BinOp op e (Const n)) reg@(dest:_) = transExp e reg ++ [transOpImm op dest n]

-- If on the left, we can use the commutative operations
transExp (BinOp Plus (Const n) e) reg@(dest:_)  = transExp e reg ++ [Add dest n]
transExp (BinOp Times (Const n) e) reg@(dest:_) = transExp e reg ++ [Mul dest n]

-- If we are on the last register, default to accumulator scheme
-- Else we use the weight function to determine which path to follow
-- e1 <- dest and e2 <- next and Instr dest next
transExp (BinOp op e1 e2) [dest] 
  = transExp e2 [dest] 
  ++ Push dest : transExp e1 [dest] 
  ++ [transOpStack op dest]
transExp (BinOp op e1 e2) (dest:next:rest)
  | weight e1 > weight e2 
    = transExp e1 (dest:next:rest) 
    ++ transExp e2 (next:rest) 
    ++ [transOp op dest next]
  | otherwise 
    = transExp e2 (next:dest:rest) 
    ++ transExp e1 (dest:rest) 
    ++ [transOp op dest next]

transExp _ [] = error "(transExp) Out of registers to use!"
