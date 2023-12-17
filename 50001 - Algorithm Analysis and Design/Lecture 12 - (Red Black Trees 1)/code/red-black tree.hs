data Colour = Red | Black

data RBTree a = Empty | Node Colour (RBTree a) a (RBTree a)
