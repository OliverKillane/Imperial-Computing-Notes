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
   = Add Reg Reg | Sub Reg Reg 
    | Mul Reg Reg | Div Reg Reg -- Op r1 r2 -> r1 := r1 <Op> r2
    | AddImm Reg Int | SubImm Reg Int 
    | MulImm Reg Int | DivImm Reg Int -- <Op>Imm r c -> r := r <Op> c 
    | AddStack Reg | SubStack Reg
    | MulStack Reg | DivStack Reg -- <Op>Imm r c -> r := r <Op> mem[SP]; SP--
    | Load Reg Name    -- Load r1 n    -> r1 := mem[n]
    | LoadImm Reg Int  -- LoadImm r1 i -> r1 := i
    | Store Reg Name   -- Load r1 n    -> mem[n] := r1
    | Push Reg         -- Push r1      -> SP++; mem[SP] := r1
    | Pop Reg          -- Pop r2       -> r1 := mem[SP]; SP--
    | CompEq Reg Reg   -- CompEq r1 r2 -> r1 := r1 - r2 = 0 ? 1 : 0
    | JTrue Reg Label  -- JTrue r1 l   -> IF r1 = 1 THEN JUMP TO l
    | JFalse Reg Label -- JFalse r1 l  -> IF r1 = 0 THEN JUMP TO l
    | Define Label     -- Assembler directive to set up label
    deriving(Show)

type Reg = Int
type Label = [Char]

-- in ghci 'transExp example 0'
example :: Exp
example = BinOp Plus (BinOp Plus (BinOp Times (Const 100) (Const 3)) (BinOp Plus (BinOp Times (Const 200) (Const 2)) (Const 300))) (BinOp Plus (Const 400) (BinOp Times (Const 500) (Const 3)))

translateOp :: Op -> (Int -> Int -> Instruction)
translateOp Plus = Add
translateOp Minus = Sub
translateOp Times = Mul
translateOp Divide = Div

translateOpImm :: Op -> (Int -> Int -> Instruction)
translateOpImm Plus = AddImm
translateOpImm Minus = SubImm
translateOpImm Times = MulImm
translateOpImm Divide = DivImm

translateOpStack :: Op -> (Int -> Instruction)
translateOpStack Plus = AddStack
translateOpStack Minus = SubStack
translateOpStack Times = MulStack
translateOpStack Divide = DivStack

maxReg :: Int
maxReg = 10

transExp :: Exp -> Reg -> [Instruction]

-- No need to check maxreg as we only use one register (a reg or the last one)
transExp (Const n) r = [LoadImm r n]
transExp (Ident id) r = [Load r id]
transExp (Unop Minus e) r = transExp e r ++ [MulImm r (-1)]
transExp (Unop _ _) _
  = error "(transExp) Only '-' unary operator supported"

-- As * and + are commutative, the order does not matter, only use one register so no need to check maxReg
transExp (BinOp Times (Const n) e) r = transExp e r ++ [MulImm r n]
transExp (BinOp Plus (Const n) e) r = transExp e r ++ [AddImm r n]

-- Can run left hand, then do right hand with immediate operand
transExp (BinOp op e (Const n)) r = transExp e r ++ [translateOpImm op r n]

-- General case for two expressions, we need to take into account the registers used.
transExp (BinOp op e1 e2) r 
  | r == maxReg = transExp e2 r ++ Push r : transExp e1 r ++ [translateOpStack op r]
  | otherwise = transExp e1 r ++ transExp e2 (r+1) ++ [translateOp op r (r+1)]
