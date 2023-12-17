data Tree a = Tip | Leaf a | Node Int (Tree a) (Tree a)

node :: Tree a -> Tree a -> Tree a
node l r = Node (size l + size r) l r

instance List Tree where
  toList :: Tree a -> [a]
  toList Tip = []
  toList (Leaf n) = [n]
  toList (Fork n l r) = toList l ++ toList r

  -- Invariant: size Node n a b = n = size a + size b
  length :: Tree a -> Int
  length Tip = 0
  length (Leaf _) = 1;
  length (Node n _ _) = n;

  (!!) :: Tree a -> Int -> a
  (Leaf x) !! 0 = x
  (Node n l r) !! k
    | k < m = l!!k
    | otherwise = r!! (k-m)
    where m = length l

  -- case for Tip !! n or Leaf !! >0
  _ !! _ = error "(!!): Cannot get list index"
