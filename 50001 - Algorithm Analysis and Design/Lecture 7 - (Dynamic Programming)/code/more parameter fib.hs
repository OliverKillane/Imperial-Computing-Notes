fib :: Int -> Integer
fib n = fibHelper n 0 1
  where
    fibHelper :: Int -> Integer -> Integer -> Integer
    fibHelper 0 x y = x
    fibHelper n x y = fibHelper (n-1) y (x + y)
