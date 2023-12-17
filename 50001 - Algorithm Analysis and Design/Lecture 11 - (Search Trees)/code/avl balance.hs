balance :: Ord a => HTree a -> a -> HTree a -> HTree
balance l x r
  | lh == lr || abs (lr - lr) == 1 = t
  | lh > lr   = rotr(hnode (if height ll < height lr then rotl l else l) x r)
  | otherwise = rotl(hnode l x (if height rl > height rr then rotr r else r))
  where
    lh = height l
    rl = height r
    (HNode _ ll _ lr) = l
    (HNode _ rl _ rr) = r