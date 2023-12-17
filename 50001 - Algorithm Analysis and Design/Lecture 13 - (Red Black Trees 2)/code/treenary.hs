-- each element is a red black tree (+ an extra root element (a))
data Digit a = One a (RBTree a) | Two a (RBTree a) a (RBTree a)

incr :: a -> RBTree a -> [Digit a] -> [Digit a]
incr x t [] = [One x t]
incr x t ((One y u) : ds) = Two x t y u : ds
incr x t ((Two y u z v) : ds) = One x t : incr y (Node Black u z v) ds