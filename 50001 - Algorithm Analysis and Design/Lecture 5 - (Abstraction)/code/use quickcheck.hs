import Test.QuickCheck

-- code to test written here ...

prop_propertyname :: InputTypes -> Bool
prop_propertyname = test code

-- example for normalise (takes a list type, that has equality defined for it)
prop_normalise (Eq a, Eq (list a), List list) => list a -> Bool
prop_normalise xs = (toList . fromList) xs == xs

-- Can return properties (requires show) using the triple-equals
prop_assoc :: (Eq (list a), Show (list a), List list) 
    => list a -> list a -> list a -> Property
prop_assoc xs ys zs = (xs ++ ys) ++ zs === xs ++ (ys ++ zs)
