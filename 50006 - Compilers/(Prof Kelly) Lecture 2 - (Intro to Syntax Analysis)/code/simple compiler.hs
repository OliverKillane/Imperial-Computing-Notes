{- 
Simple compiler example:
Arithmetic Expressions -> Stack Machine Instructions

Original Description:
"Compiling arithmetic expressions into code for a stack machine.  This is not a 
solution to Exercise 2 - it's an executable version of the code generator for 
expressions, which is given in the notes.  Build on it to yield a code generator
for statements.

Paul Kelly, Imperial College, 2003

Tested with Hugs (Haskell 98 mode), Feb 2001 version"

Changes:
- This version has been updated to work with Haskell version 8.6.5
- Use of where over let & general refactoring
- Fixed bug with execute (missing patterns for invalid stack instructions)
- New grammar to support multiplication and division

Grammar:
 add    -> mul + add | mul - add | mul
 mul    -> factor * mul | factor / mul | factor
 factor -> number | identifier

+ - (right associative, low precedence)
* / (right associative, high precedence)

Eg:
> tokenise "a+b*17"
[IDENT a,PLUS,IDENT b,MUL,NUM 17]

> parser (tokenise "a+b-17") 
Plus (Ident a, Minus (Ident b, Num 17))

> parser (tokenise "3-3-3*77*a-4")
Minus (Num 3, Minus (Num 3, Minus (Mul (Num 3, Mul (Num 77, Ident a)), Num 4)))

> compile "a+b+c*7-3"
[PushVar a,PushVar b,PushVar c,PushConst 7,MulToS,PushConst 3,SubToS,AddToS,AddToS]

> translate (parser (tokenise "a+b/17"))
[PushVar a,PushVar b,PushConst 17,DivToS,AddToS]

> putStr (runAnimated [("a", 9)] [] (translate (parser (tokenise "100+a*3-17"))))
[100]
[9,100]
[3,9,100]
[27,100]
[17,27,100]
[10,100]
[110]
[110]

-}

import Data.Char ( isDigit, isAlpha, digitToInt )
import Text.Parsec (tokens, Stream (uncons))

-- Token data type
data Token 
  = IDENT [Char] | NUM Int | PLUS | MINUS | MUL | DIV

-- Ast (abstract syntax tree) data type
data Ast 
  = Ident [Char] | Num Int | Plus Ast Ast | Minus Ast Ast | Mul Ast Ast | Div Ast Ast

-- Instruction data type
-- 
-- PushConst pushes a given number onto the stack; AddToS takes the top
-- two numbers from the top of the stack (ToS), and them and pushes the sum.
-- (We have to invent new names to avoid clashing with MUL, Mul etc above)
data Instruction 
  = PushConst Int | PushVar [Char] | AddToS | SubToS | MulToS | DivToS

instance Show Token where
  showsPrec p (IDENT name) = showString "IDENT " . showString name
  showsPrec p (NUM num) = showString "NUM " . shows num
  showsPrec p (PLUS) = showString "PLUS"
  showsPrec p (MINUS) = showString "MINUS"
  showsPrec p (MUL) = showString "MUL"
  showsPrec p (DIV) = showString "DIV"

instance Show Ast where
  showsPrec p (Ident name) = showString "Ident " . showString name
  showsPrec p (Num num) = showString "Num " . shows num
  showsPrec p (Plus e1 e2) = showString "Plus (" . shows e1 . showString ", " . shows e2 . showString ")" 
  showsPrec p (Minus e1 e2) = showString "Minus (" . shows e1 . showString ", " . shows e2 . showString ")" 
  showsPrec p (Mul e1 e2) = showString "Mul (" . shows e1 . showString ", " . shows e2 . showString ")" 
  showsPrec p (Div e1 e2) = showString "Div (" . shows e1 . showString ", " . shows e2 . showString ")" 

instance Show Instruction where
  showsPrec p (PushConst n) = showString "PushConst " . shows n
  showsPrec p (PushVar name) = showString "PushVar " . showString name
  showsPrec p AddToS = showString "AddToS"
  showsPrec p SubToS = showString "SubToS"
  showsPrec p MulToS = showString "MulToS"
  showsPrec p DivToS = showString "DivToS"

-- Parse the tokens (top-down) by parsing each expression to get a new parse 
-- tree and the rest of the tokens. No tokens should remain after parsing.
parser :: [Token] -> Ast
parser tokens
  | null rest = tree
  | otherwise = error "(parser) excess rubbish"
  where
    (tree, rest) = parseAdd tokens

parseAdd :: [Token] -> (Ast, [Token])
parseAdd tokens
  = case rest of
      (PLUS : rest2) -> let (subexptree, rest3) = parseAdd rest2 in (Plus multree subexptree, rest3)
      (MINUS : rest2) -> let (subexptree, rest3) = parseAdd rest2 in (Minus multree subexptree, rest3)
      othertokens -> (multree, othertokens)
  where
    (multree, rest) = parseMul tokens

parseMul :: [Token] -> (Ast, [Token])
parseMul tokens
  = case rest of 
      (MUL : rest2) -> let (subexptree, rest3) = parseMul rest2 in (Mul factortree subexptree, rest3)
      (DIV : rest2) -> let (subexptree, rest3) = parseMul rest2 in (Div factortree subexptree, rest3)
      othertokens -> (factortree, othertokens)
  where
    (factortree, rest) = parseFactor tokens

parseFactor :: [Token] -> (Ast, [Token])
parseFactor ((NUM n):restoftokens) = (Num n, restoftokens)
parseFactor ((IDENT x):restoftokens) = (Ident x, restoftokens)
parseFactor [] = error "(parseFactor) Attempted to parse empty list"
parseFactor (t:_) = error $ "(parseFactor) error parsing token " ++ show t


-- Lexical analysis - tokenisation
tokenise :: [Char] -> [Token]
tokenise [] = []                    -- (end of input)
tokenise (' ':rest) = tokenise rest      -- (skip spaces)
tokenise ('+':rest) = PLUS : (tokenise rest)
tokenise ('-':rest) = MINUS : (tokenise rest)
tokenise ('*':rest) = MUL : (tokenise rest)
tokenise ('/':rest) = DIV : (tokenise rest)
tokenise (ch:rest)
  | isDigit ch  = (NUM dn):(tokenise drest2)
  | isAlpha ch  = (IDENT an):(tokenise arest2)
  where
    (dn, drest2) = convert (ch:rest)
    (an, arest2) = getname (ch:rest)
tokenise (c:_) = error $ "(tokenise) unexpected character " ++ [c]

getname :: [Char] -> ([Char], [Char]) -- (name, rest)
getname = flip getname' []
  where
      getname' :: [Char] -> [Char] -> ([Char], [Char])
      getname' [] chs = (chs, [])
      getname' (ch : str) chs
        | isAlpha ch = getname' str (chs++[ch])
        | otherwise  = (chs, ch : str)

convert :: [Char] -> (Int, [Char])
convert = flip conv' 0
  where
    conv' [] n = (n, [])
    conv' (ch : str) n
      | isDigit ch = conv' str ((n*10) + digitToInt ch)
      | otherwise  = (n, ch : str)

-- Translate - the code generator
translate :: Ast -> [Instruction]
translate (Num n) = [PushConst n]
translate (Ident x) = [PushVar x]
translate (Plus e1 e2) = translate e1 ++ translate e2 ++ [AddToS]
translate (Minus e1 e2) = translate e1 ++ translate e2 ++ [SubToS]
translate (Mul e1 e2) = translate e1 ++ translate e2 ++ [MulToS]
translate (Div e1 e2) = translate e1 ++ translate e2 ++[DivToS]

compile :: [Char] -> [Instruction]
compile = translate . parser . tokenise

-- Execute, run - simulate the machine running the stack instructions
--
-- Note that this simple machine is too simple to be realistic; 
-- (1) 'execute' doesn't return the store, so no instruction can change it
-- (2) 'run' forgets each instruction as it is executed, so can't do loops

-- The state of the machine consists of a store (a set of associations 
-- between variable and their values), together with a stack:

type Stack = [Int]
type Store = [([Char], Int)]

-- 'run' executes a sequence of instructions using a specified
-- store, and starting from a given stack
--
run :: Store -> Stack -> [Instruction] -> Stack

run store stack [] = stack
run store stack (i : is) = run store (execute store stack i) is

-- 'execute' applies a given instruction to the current state of the
-- machine - ie the store and the stack
--
execute :: Store -> Stack -> Instruction -> Stack 
execute store (a : b: rest) AddToS        = ( (b+a) : rest )
execute store (a : b: rest) SubToS        = ( (b-a) : rest )
execute store (a : b: rest) MulToS        = ( (b*a) : rest )
execute store (a : b: rest) DivToS        = ( (b `div` a) : rest )
execute store rest          (PushConst n) = ( n : rest )
execute store rest          (PushVar x)   = ( n : rest )
  where n = valueOf x store
execute store [x] instr = error $ "(execute) attempted to run " ++ show instr ++ " with only" ++ show x ++ " on the stack"
execute store []  instr = error $ "(execute) attempted to run " ++ show instr ++ " with an empty stack"

valueOf x [] = error ("no value for variable "++show x)
valueOf x ( (y,n) : rest ) = if x==y then n else valueOf x rest

-- runAnimated does what run does but shows the stack after each step:
--
runAnimated :: Store -> Stack -> [Instruction] -> [Char]
runAnimated store stack [] = show stack
runAnimated store stack (i : is) = show newstack ++ "\n" ++ runAnimated store newstack is
  where
    newstack = execute store stack i


