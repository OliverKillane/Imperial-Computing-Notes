import System.Random (StdGen, mkStdGen, random)
-- node random :: StdGen -> (Int, StdGen)

data RTreap a = RTreap StdGen (Treap a)

insert :: Ord a => a -> RTreap a -> RTreap a
insert x (RTreap seed t) = RTreap seed' (pinsert x p t) 
  where (p, seed') = random seed

-- note 42 is used for 
empty :: RTreap a
empty = RTreap (mkStdGen 42) Empty

-- Build up tree, requires O(n log n)
fromList :: Ord a => [a] -> RTreap a
fromList xs = foldr insert empty xs

-- Linear time conversion (use treap tolist)
toList :: RTreap a -> [a]
toList (RTreap _ t) = tolist t

-- Randomiozed Quicksort O(n log n)
-- Effectively the random priorities are the partitions, first pivot is the 
-- highest priority.
rquicksort :: Ord a => [a] -> [a]
rquicksort = toList . fromList