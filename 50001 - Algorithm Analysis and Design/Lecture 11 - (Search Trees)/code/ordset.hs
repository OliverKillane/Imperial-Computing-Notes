class OrdSet ordset where
  empty    :: ordset n
  insert   :: Ord a => a -> ordset a -> ordset a
  member   :: Ord a => a -> ordset a -> Bool
  fromList :: Ord a => [a] -> ordset a
  toList   :: Ord a => ordset a -> [a]