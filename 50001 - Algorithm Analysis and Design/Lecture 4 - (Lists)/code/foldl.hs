foldl :: (b -> a -> b) -> b -> [a] -> b
foldl f k []     = k
foldl f k (x:xs) = foldl f (f k x) xs