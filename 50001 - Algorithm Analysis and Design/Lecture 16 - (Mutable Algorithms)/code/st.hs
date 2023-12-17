
-- State Transformer (ST) takes a state s and return value a.
-- "Give me any program with any state s, and if it returns an a, so will I".
runST :: (forall s . ST s a) -> a

-- Take a value a, produces a program with some state s, that returns a 
-- reference with that state and the value stored.
newSTRef :: a -> ST s (STRef s a)

-- Takes in a reference in some state s, performs a computation to get a
readSTRef :: STRef s a -> ST s a

-- Take in a reference, and a new value a, performing a computation to update
-- the referenced value (update does not return anything itself, hence ()).
writeSTRef :: STRef s a -> a -> ST s ()

-- Takes a value, returns a computation that executes in any state s to return 
-- an a.
return :: a -> ST s a