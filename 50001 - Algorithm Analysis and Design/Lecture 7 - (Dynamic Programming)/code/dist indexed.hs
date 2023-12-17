dist :: String -> String -> Int
dist xs ys = dist' xs ys (length xs) (length ys)

dist' :: String -> String -> Int -> Int -> Int
dist' xs ys i 0 = i
dist' xs ys 0 j = j
dist' xs ys i j
  = minimum [dist' xs ys i (j-1) + 1,
             dist' xs ys (i-1) j + 1,
             dist' xs ys (i-1) (j-1) + if x == y then 0 else 1]
  where
    m = length xs
    n = length ys
    x = xs !! (m-i)
    y = ys !! (n-j)