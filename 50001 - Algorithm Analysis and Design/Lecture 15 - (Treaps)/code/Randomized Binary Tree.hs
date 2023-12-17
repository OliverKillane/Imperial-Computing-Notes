import System.Random (StdGen, mkStdGen, randomR)

data BTree a = Empty | Node (BTree a) a (BTree a)

insert :: Ord a => a -> BTree a -> BTree a
insert x Empty = Node Empty x Empty
insert x t@(Node l y r)
  | x == y = t
  | x < y = Node (insert x l) y r
  | otherwise = Node l y (insert x r)

-- basic lefty/right rotations
rotr :: BTree a -> a -> BTree a -> BTree a
rotr (Node a x b) y c = Node a x (Node b y c)
rotr _ _ _= error "(rotr): left was empty"

rotl :: BTree a -> a -> BTree a -> BTree a
rotl a x (Node b y c) = Node (Node a x b) y c
rotl _ _ _= error "(rtol): right was empty"


-- Insert to the root of the tree (maintaining order)
insertRoot :: Ord a => a -> BTree a -> BTree a
insertRoot x Empty = Node Empty x Empty
insertRoot x t@(Node l y r)
  | x == y = t
  | x < y = rotr (insertRoot x l) y r
  | otherwise = rotl l y (insertRoot x r)

-- Randomized binary tree
data RBTree a = RBTree StdGen Int (BTree a)

empty :: RBTree a
empty = RBTree (mkStdGen 42) 0 Empty

-- chance of 1 / n+1 of inserting at root.
insert' :: Ord a => a -> RBTree a -> RBTree a
insert' x (RBTree seed n t) = RBTree seed' (n+1) (f x t)
  where
    f = case p of
      0 -> insertRoot
      _ -> insert
    (p, seed') = randomR (0,n) seed