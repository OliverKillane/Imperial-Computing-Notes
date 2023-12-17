data Peano = Zero | Succ Peano

-- analogous to (:) Cons
incr :: Peano -> Peano
incr = Succ

-- analogous to tail
decr :: Peano -> Peano
decr (Succ n) = n
decr Zero = error "Cannot decrement zero"

-- analogous to (++) concatenate
add :: Peano -> Peano -> Peano
add a Zero = a
add a (Succ b) = Succ (add a b)

-- tail recursive version for extra goodness!
add a b = add (incr a) (decr b)
