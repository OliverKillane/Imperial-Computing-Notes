insert :: Int -> [Int] -> [Int]
insert x [] = [x]
insert x yss@(y:ys)
    | x <= y    = x:yss
    | otherwise = y : insert x ys