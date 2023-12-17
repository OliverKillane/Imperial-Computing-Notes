concat :: [[a]] -> [a]
concat []       = []
concat (xs:xss) = xs ++ concat xss
