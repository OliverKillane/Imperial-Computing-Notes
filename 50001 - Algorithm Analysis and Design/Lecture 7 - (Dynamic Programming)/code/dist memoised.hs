import Data.Array ( Array, (!) )

dist :: String -> String -> Int
dist xs ys = table ! (m,n)
  where
    table = tabulate ((0,0),(m,n)) (uncurry memo)
    
    memo :: Int -> Int -> Int
    memo i 0 = i
    memo 0 j = j
    memo i j 
      = minimum [table ! (i, j - 1) + 1,
                 table ! (i-1,j) + 1,
                 table ! (i - 1,j - 1) + if x == y then 0 else 1]
      where
        x = ays ! (m - i)
        y = ays ! (n - j)
    
    m = length xs
    n = length ys
    axs,ays :: Array Int Char 
    axs = fromList xs
    ays = fromList ys