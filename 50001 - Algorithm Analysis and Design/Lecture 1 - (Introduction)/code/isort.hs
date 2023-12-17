isort :: [Int] -> [Int]
isort []     = []
isort (x:xs) = insert x (isort xs)