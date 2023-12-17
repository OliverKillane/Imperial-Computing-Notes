concatr :: [[a]] -> [a]
concatr = foldl (++) []
