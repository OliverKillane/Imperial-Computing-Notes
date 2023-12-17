data Tree a = Tip | Leaf a | Node Int (Tree a) (Tree a)

type RAList a = [Tree a]

instance List RAList where
  toList :: RAList a -> [a]
  toList (RaList ls) = concatMap toList ls

  fromList :: [a] -> RAList a
  fromList = foldr (:) empty

  empty :: RAList a
  empty = []

  (:) :: a -> RAList a -> RAList a
  n : [] = [Leaf n]
  n : (RAList ls) = RAList (insertTree (Leaf n) ls)
    where
      insertTree :: Tree a -> [Tree a] -> [Tree a]
      insertTree t ([])      = [t]
      insertTree t (Tip:ls) = t:ls
      insertTree t (t':ts)  = Tip: insertTree (node t t') ts

  length :: RAList a -> Int
  length (RAList ls) = foldr ((+) . length) 0 ls
  
  (!!) :: RAList a -> Int -> a
  (RAList []) !! _ = error "(!!): empty list"
  (RAList (x:xs)) !! n
    | isEmpty x = (RAList ts) !! k
    | n < m     = x !! n
    | otherwise = (RAList xs) !! (n-m)
    where m = length x
