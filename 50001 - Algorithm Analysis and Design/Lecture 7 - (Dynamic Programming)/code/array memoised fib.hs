import Data.Array ( Array, (!) )

fib :: Int -> Integer
fib n = table ! n
  where
    table :: Array Int Integer
    table = tabulate (0,n) memo

    memo :: Int -> Integer
    memo 0 = 0
    memo 1 = 1
    memo n = table ! (n-2) + table ! (n-1)
