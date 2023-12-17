import Data.Array.MArray (MArray(newArray))
import Data.Array.ST
import Control.Monad.ST
import Data.List ((\\))

-- immutable
minfree :: [Int] -> Int
minfree xs = head ( [0..] \\ xs )

-- effectively the same as minfree
minfree' :: [Int] -> Int
minfree' xs = head . filter(not . (`elem` xs)) $ [0..]


-- Builds up an array of which are present, 
minfreeMut :: [Int] -> Int
minfreeMut = length . takeWhile id . checklist

{- 
Build an array, at each index True/False for if the index is in xs
We only need to use an array of size (length xs) as we do not care about 
natural numbers larger than this (if they are in the list, then a smaller 
natural number was missed).

xs [0,1,2,3,6,7,8]
ys [T,T,T,T,F,F,T] ... (don't care about 7 or 8)

-}
checklist :: [Int] -> [Bool]
checklist xs  = runST $ do {
  ys <- newArray (0,l - 1) False :: ST s (STArray s Int Bool);
  sequence [writeArray ys x True | x <- xs, x < l];
  getElems ys;
  }
  where
    l = length xs
