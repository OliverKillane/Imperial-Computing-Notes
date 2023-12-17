class List list where
    empty :: list a
    single :: a -> list a

    (:) :: a -> list a -> list a
    snoc :: list a -> list a -> list a

    head :: list a -> a
    tail :: list a -> list a

    last :: list a -> a
    init :: list a -> list a

    (++) :: list a -> list a -> list a

    length :: list a -> Int
    
    fromList :: [a] -> list a
    toList :: list a -> [a]