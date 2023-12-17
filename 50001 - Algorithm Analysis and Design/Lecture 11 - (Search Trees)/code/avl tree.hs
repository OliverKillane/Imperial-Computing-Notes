-- H for height! The int stored at a node is the height of that tree.
data HTree a = HTip | HNode Int (HTree a) a (HTree a)

height :: HTree a -> Int
height HTip = 0
height (HNode h _ _ _) = h

hnode :: HTree a -> a -> HTree a -> HTree a
hnode l x r = HNode h l x r 
  where h = max (height l) (height r) + 1
