blacken :: Ord a => RBTree a -> RBTree a
blacken (Node Red l x r) = Node Black l x r
blacken t                = t

balance :: Ord a => Colour -> RBTree a -> a -> RBTree a -> RBTree a
balance c l v r = case Node c l v r of
  Node Black (Node Red (Node Red a x b) y c) z d -> bal x y z a b c d
  Node Black (Node Red a x (Node Red b y c)) z d -> bal x y z a b c d
  Node Black a x (Node Red (Node Red b y c) z d) -> bal x y z a b c d
  Node Black a x (Node Red b y (Node Red c z d)) -> bal x y z a b c d
  t                                              -> t
  where
    bal x y z a b c d = Node Red (Node Black a x b) y (Node Black c z d)

insert :: Ord a => a -> RBTree a -> RBTree a
insert = (blacken .) . ins
  where
    ins :: Ord a => a -> RBTree a -> RBTree a
    ins x Empty = Node Red Empty x Empty
    ins x t@(Node c l y r)
      | x < y     = balance c (ins x l) y r
      | x == y    = t
      | otherwise = balance c l y (ins x r)