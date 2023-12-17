fromOrdList :: Ord a => [a] -> RBTree a
fromOrdList = foldr insert Empty