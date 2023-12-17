data List [a] = [] | (:) a [a] 

-- or...
data List a where
    Empty :: List a
    Cons :: a -> List a -> List a