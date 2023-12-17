-- fold left to combine the digits together into a tree
fromList :: [a] -> RBTree a
fromList xs = foldl link Empty (foldr add xs)

link :: RBTree a -> Digit a -> RBTree a
link l (One x t) = Node Black l x t
link l (Two x t y u) = Node Black (Node Red l x t) y u 