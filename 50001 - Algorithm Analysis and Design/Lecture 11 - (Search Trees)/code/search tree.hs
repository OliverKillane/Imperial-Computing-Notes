data Tree a = Tip | Node (Tree a) a (Tree a)

instance OrdSet Tree where
  empty :: Tree n
  empty = Tip

  insert :: Ord a => a -> Tree a -> Tree a
  insert x Tip = Node Tip x Tip
  insert x (Node l y r)
    | x == y    = t
    | x < y     = Node (insert x l) y r
    | otherwise = Node l y (insert x r)
  
  member :: Ord a => a -> Tree a -> Bool
  member x Tip = False
  member x (Node l y r)
    | x == y    = True
    | x < y     = member x l
    | otherwise = member x r

  fromList :: Ord a => [a] -> Tree a
  fromList = foldr insert empty
  
  toList :: Ord a => Tree a -> [a]
  toList Tip          = []
  toList (Node l y r) = toList l ++ y:toList r