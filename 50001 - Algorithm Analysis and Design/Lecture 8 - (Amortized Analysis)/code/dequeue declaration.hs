-- can ignore certain patterns due to invariant
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

data Dequeue a = Dequeue [a] [a]

instance List Dequeue where
  toList :: Dequeue a -> [a]
  toList (Dequeue us sv) = us ++ reverse sv

  fromList :: [a] -> Dequeue a
  fromList xs = Dequeue us (reverse vs) 
    where (us,vs) = splitAt (length xs `div` 2) xs

  -- use the invariant, if [] sv then sv = [x] or []

  -- O(1)
  cons :: a -> Dequeue a -> Dequeue a
  cons x (Dequeue us []) = Dequeue [x] us
  cons x (Dequeue us sv) = Dequeue (x:us) sv

  -- O(1)
  snoc :: Dequeue a -> a -> Dequeue a
  snoc (Dequeue [] sv) x = Dequeue sv [x]
  snoc (Dequeue us sv) x = Dequeue us (x:sv)

  -- O(1)
  last :: Dequeue a -> a
  last (Dequeue _ (s:_)) = s
  last (Dequeue [u] _) = u
  last (Dequeue [] []) = error "Nothing in the dequeue"

  -- O(1)
  head :: Dequeue a -> a
  head (Dequeue (u:_) _) = u
  head (Dequeue [] [v]) = v
  head (Dequeue [] []) = error "Nothing in the dequeue"

  -- O(1)
  tail :: Dequeue a -> Dequeue a
  tail (Dequeue [] []) = error "Nothing in the dequeue"
  tail (Dequeue [] _) = empty
  tail (Dequeue _ []) = empty
  tail (Dequeue [u] sv) = Dequeue (reverse su) 
    where
      n = length sv
      (su, sv') = splitAt (n `div` 2) sv
      -- note: could also do a fromList (reverse sv) but less efficient

  tail (Dequeue (u:us) sv) = Dequeue us sv

  -- O(1)
  init :: Dequeue a -> Dequeue a
  init (Dequeue [] []) = error "Nothing in the dequeue"
  init (Dequeue [] _) = empty
  init (Dequeue _ []) = empty
  init (Dequeue us [s]) = fromList us
  init (Dequeue us (s:sv)) = Dequeue us sv

  isEmpty :: Dequeue a -> Bool 
  isEmpty (Dequeue [] []) = True
  isEmpty _ = False

  empty :: Dequeue a
  empty = Dequeue [] []

