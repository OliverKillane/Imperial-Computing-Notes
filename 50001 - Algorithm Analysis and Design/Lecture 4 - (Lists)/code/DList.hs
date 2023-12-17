newtype DList a = DList ([a] -> [a])

instance List DList where
    toList :: DList a -> [a]
    toList (DList fxs) = fxs []

    fromList :: [a] -> DList a
    fromList xs = DList (xs++)

    (++) :: DList a -> DList a -> DList a
    DList fxs ++ DList fys = DList(fxs . fys)
