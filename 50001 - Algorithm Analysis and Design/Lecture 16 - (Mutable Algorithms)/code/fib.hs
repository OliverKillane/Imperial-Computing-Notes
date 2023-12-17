import Data.STRef (newSTRef, readSTRef, writeSTRef)
import Control.Monad.ST (runST)

-- immutable looping fibonacci
fib :: Int -> Integer
fib n = loop n 0 1
  where 
    loop :: Int -> Integer -> Integer -> Integer
    loop 0 x y = x
    loop n x y = loop (n-1) y (x+y)

-- mutable looping fibonacci
fib0 :: Int -> Integer
fib0 n = runST $ do
  rx <- newSTRef 0
  ry <- newSTRef 1
  let loop 0 = do readSTRef rx
      loop n = do {
        x <- readSTRef rx;
        y <- readSTRef ry;
        writeSTRef rx y;
        writeSTRef ry (x + y);
        loop (n - 1);}
  loop n