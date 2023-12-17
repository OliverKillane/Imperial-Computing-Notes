concatr :: [[a]] -> [a]
concatr = foldr (++) []
