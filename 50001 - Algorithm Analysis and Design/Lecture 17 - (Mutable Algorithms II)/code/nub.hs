import Control.Monad (when)
import Data.Array.ST
    ( getElems, newListArray, readArray, writeArray, STArray )
import Control.Monad.ST ( ST, runST )


-- immutable version:
nub :: Eq a => [a] -> [a]
nub = reverse . foldl nubHelper []
  where
    nubHelper :: Eq a => [a] -> a -> [a]
    nubHelper ns c
      | c `elem` ns = ns
      | otherwise   = c:ns

-- mutable version, create a hash table of characters to track which have 
-- already been seen.
nubMut :: (Hashable a, Eq a) => [a] -> [a]
nubMut xs = concat $ runST $ do
  axss <- newListArray (0, n - 1) (replicate 256 [ ]) :: ST s (STArray s Int [a])
  sequence [do {
    let hx = hash x `mod` (n - 1)
    ys <- readArray axss hx
    unless (x `elem` ys) $ do writeArray axss hx (x : ys)}
  | x <- xs]
  getElems axss
  where
    -- number of buckets in the hash table
    n = 256