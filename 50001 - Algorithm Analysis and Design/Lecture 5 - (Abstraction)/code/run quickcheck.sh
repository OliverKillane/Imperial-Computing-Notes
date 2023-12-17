ghci file_to_check.hs
*file_to_check> quickCheck (prop_normalise :: [Int] -> Bool)
+++ OK, passed 100 tests.
*file_to_check> quickCheck (prop_normalise :: [Bool] -> Bool)
+++ OK, passed 100 tests.
*file_to_check> verboseCheck (prop_normalise :: [Bool] -> Bool)
Passed:
...

Passed:
...

etc...

+++ OK, passed 100 tests.