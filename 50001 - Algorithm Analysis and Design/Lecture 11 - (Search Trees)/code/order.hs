class Eq a => Ord a where
    (<=) :: a -> a -> Bool
    (<)  :: a -> a -> Bool
    (>=) :: a -> a -> Bool
    (>)  :: a -> a -> Bool