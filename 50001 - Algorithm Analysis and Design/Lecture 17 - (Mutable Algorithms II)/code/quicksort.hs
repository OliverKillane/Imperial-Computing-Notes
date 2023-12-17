import Data.Array.ST ( readArray, writeArray, STArray, getElems )
import Control.Monad.ST ( ST )

-- swap elements over (classic store in temp & swap over other before writeback)
swap :: STArray s Int a -> Int -> Int -> ST s ()
swap axs i j = do
  temp <- readArray axs i
  readArray axs j >>= writeArray axs i
  writeArray axs j temp

qsort :: Ord a => [a] -> [a]
qsort xs = runST $ do
  axs <- newListArray (0,n) xs
  aqsort axs 0 n
  getElems axs
  where
    n = length xs - 1

{- 
Partition around a pivot (k) (all smaller to left, larger to right
(unsorted)), then recur on these partitions
Index:     0      (k-1) k (k+1)    n
Contents: [ ..<= x .. ][x][ .. >x ..]
-}
aqsort :: Ord a => STArray s Int a -> Int -> Int -> ST s ()
aqsort axs i j
  | i >= j = return ()
  | otherwise = do
      k <- apartition axs i j
      aqsort axs i (k - 1)
      aqsort axs (k + 1) j

apartition :: Ord a => STArray s Int a -> Int -> Int -> ST s Int
apartition asx p q = do
  x <- readArray axs p
  let loop i j
    | i > j = do 
      swap axs p j
      return j
    | otherwise = do 
      u <- readArray axs i
      if u < x
        then do loop (i + 1) j
        else do
          swap axs i j
          loop i (j - 1)
  loop (p+1) q