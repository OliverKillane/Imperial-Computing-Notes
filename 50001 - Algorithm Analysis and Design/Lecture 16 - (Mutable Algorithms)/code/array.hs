import Control.Monad.ST
import Data.Array.ST

-- Use indexable i, range, default to get a mutable array in some state
newArray :: Ix i => (i,i) -> a -> ST s (STArray s i a)

-- Use indexable i, a mutable array and return the value a with state s
readArray :: Ix i -> STArray s i a -> i -> ST s a

-- Use indexable i, a mutable array, and the value to place, return a
-- computation that updates the array (new state) but returns no value.
-- note:
writeArray :: Ix i => STArray s i a -> i -> a -> ST s ()