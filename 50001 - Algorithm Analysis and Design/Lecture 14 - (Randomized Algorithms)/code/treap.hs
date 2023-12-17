-- Node contains child treaps, as well as value (a) and the priority (Int)
data Treap a = Empty | Node (Treap a) a Int (Treap a)

-- Normal tree search using values
member :: Ord a => a -> Treap a -> Bool
member x (Node l y _ r)
  | x == y    = True
  | x < y     = member x l
  | otherwise = member x r
member _ Empty = False

-- Priority based insert
pinsert :: Ord a => a -> Int -> Treap a -> Treap a
pinsert x p Empty = Node Empty x p Empty
pinsert x p t@(Node l y q r)
  | x == y    = t
  | x < y     = lnode (pinsert x p l) y q r
  | otherwise = rnode l y q (pinsert x p r)

-- rotate right (check left node)
lnode :: Treap a -> a -> Int -> Treap a -> Treap a
lnode Empty y q r = Node Empty y q r
lnode l@(Node a x p b) y q c 
  | q > p     = Node a x p (Node b y q c)
  | otherwise = Node l y q c

-- rotate left (check right node)
rnode :: Treap a -> a -> Int -> Treap a -> Treap a
rnode l y q Empty = Node l y q Empty
rnode a x p r@(Node b y q c)
  | q < p     = Node (Node a x p b) y q c
  | otherwise = Node a x p r

-- delete node by recursively searching, then delete and merge subtrees
delete :: Ord a => a -> Treap a -> Treap a
delete x Empty = Empty
delete x (Node a y q b)
  | x == y    = merge a b
  | x < y     = Node (delete x a) y q b
  | otherwise = Node a y q (delete x b)

merge :: Treap a -> Treap a -> Treap a
merge Empty r = r
merge l Empty = l
merge l@(Node a x p b) r@(Node c y q d)
  | p < q     = Node a x p (merge b r)
  | otherwise = Node (merge l c) y q d