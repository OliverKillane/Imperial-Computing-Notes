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

data Instruction = Add | Sub | Mul | Div --
  | AddImm Int | SubImm Int | MulImm Int | DivImm Int   --
  | CompEq       -- CompEq   -> Acc := 
  | Push         -- Push     -> SP--; mem[SP] := Acc
  | Pop          -- Pop      -> Acc := mem[SP]; SP++
  | Load Name    -- Load n   -> Acc := mem[n]
  | LoadImm Int  -- Load i   -> Acc := i
  | Store Name   -- Store n  -> mem[n] := Acc
  | Jump Label   -- Jump l   -> PC := l
  | JTrue Label  -- JTrue l  -> IF Acc = 1 THEN JUMP TO l
  | JFalse Label -- JFalse l -> IF Acc = 0 THEN JUMP TO l
  | Define Label -- Assembler directive to set up label
  deriving(Show)

type Label = [Char]

-- in ghci 'transExp example'
example :: Exp
example = BinOp Plus (BinOp Plus (BinOp Times (Const 100) (Const 3)) (BinOp Plus (BinOp Times (Const 200) (Const 2)) (Const 300))) (BinOp Plus (Const 400) (BinOp Times (Const 500) (Const 3)))

transOpImm :: Op -> (Int -> Instruction)
transOpImm Plus = AddImm
transOpImm Minus = SubImm
transOpImm Times = MulImm
transOpImm Divide = DivImm

transOp :: Op -> Instruction
transOp Plus = Add
transOp Minus = Sub
transOp Times = Mul
transOp Divide = Div

transExp :: Exp -> [Instruction]
transExp (Const n) = [LoadImm n]
transExp (Ident x) = [Load x]
transExp (Unop Minus e) = transExp e ++ [MulImm (-1)]

-- Can only use Minus unary operator (e.g -3)
transExp (Unop _ _)
  = error "(transExp) Only '-' unary operator supported"

-- If constant on the left, can use immediate operand
transExp (BinOp op e (Const n)) = transExp e ++ [transOpImm op n]

-- With commutative operator, can switch order to use immediate operand
transExp (BinOp Times (Const n) e) = transExp e ++ [MulImm n]
transExp (BinOp Plus (Const n) e) = transExp e ++ [AddImm n]

-- General case for two expressions
transExp (BinOp op e1 e2) = transExp e2 ++ Push : transExp e1 ++ [transOp op]