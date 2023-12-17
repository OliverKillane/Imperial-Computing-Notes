dist :: String -> String -> Int
dist xs [] = length xs
dist [] ys = length ys
dist xxs@(x:xs) yys@(y:ys) 
  = minimum 
    [dist xxs ys + 1,
     dist xs yys + 1,
     dist xs ys + if x == y then 0 else 1]
