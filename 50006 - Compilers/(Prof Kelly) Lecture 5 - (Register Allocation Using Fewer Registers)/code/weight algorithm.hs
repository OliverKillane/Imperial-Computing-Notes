weight :: Exp -> Int
weight (Const _) = 1
weight (Ident _) = 1
weght (BinOp _ e1 e2)
    = min e1first e2first
    where
        e1first = max (weight e1) (weight e2 + 1)
        e2first = max (weight e2) (weight e1 + 1)