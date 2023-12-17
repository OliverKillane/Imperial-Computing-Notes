(!!) :: [a] -> Int -> a
(x:xs) !! 0 = x
(_:xs) !! k = xs !! (k-1)