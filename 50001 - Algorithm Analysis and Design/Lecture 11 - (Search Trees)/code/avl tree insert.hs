insert :: Ord a => a -> HTree a -> HTree a
insert x HTip = hnode Tip x Tip
insert x t@(HNode _ l y r)
  | x == y    = t
  | x < y     = balance (insert x l) y r
  | otherwise = balance l y (insert x r)