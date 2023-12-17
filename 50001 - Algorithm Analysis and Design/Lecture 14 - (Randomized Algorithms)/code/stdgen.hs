import System.Random (StdGen)

-- Create a source of randomness from an integer seed
mkStdGen :: Int -> StdGen

-- Generate a random interger, and a new source of randomness
random :: StdGen -> (Int, StdGen)

-- Generate an infinite list of random numbers using an initial seed 
-- (source of random).
randoms :: StdGen -> [Int]
randoms seed = x:randoms seed' where (x, seed') = random seed

-- In order to generate random value for any type, a typeclass is used
class Random a where
  random  :: StdGen -> (a, StdGen)
  randoms :: StdGen -> [a]

  -- Random over a (R)ange
  randomR :: (a,a)  -> StdGen -> (a, StdGen)
  randomRs:: (a,a)  -> StdGen -> [a]