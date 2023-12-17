-- Array Data Type
import Data.Array ( Ix(range), Array, array )

-- Tabulate function
tabulate :: Ix i => (i,i) -> (i -> e) -> Array i e
tabulate (a,b) f = array (a,b) [(i,f i) | i <- range (a,b)]

-- Ix (class of all indexes)

-- T(!) is in O(1)
(!) :: Ix i => Array i e -> i -> e

-- Range creates a lits of indexes in a range
range :: Ix i => (i,i) -> [i]

-- Array function creates an array from a range of indexes & values
array :: Ix i => (i,i) -> [(i,e)] -> Array i e