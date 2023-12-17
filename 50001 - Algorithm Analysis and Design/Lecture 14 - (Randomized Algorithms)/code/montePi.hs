import Control.Monad.Random (getRandomR, randomRs, MonadRandom)
import System.Random (mkStdGen, StdGen)

-- Here we can use one quarter of the circle, hence if the distance from the 
-- bottom left (0,0) to the point is within 1 then it is in the circle.
inside :: Double -> Double -> Bool
inside x y = 1 >= x * x + y * y

-- Take 1000 samples and return 4 * the proportion.
montePi :: MonadRandom m => m Double
montePi = loop samples 0
  where 
    samples = 10000
    loop 0 m = return (4 * fromIntegral m / fromIntegral samples)
    loop n m = do 
      x <- getRandomR (0,1)
      y <- getRandomR (0,1)
      loop (n-1) (if inside x y then m + 1 else m)




-- Using a stream of random numbers (RandomRs)

-- Get pairs of random numbers from the stream
pairs :: [a] -> [(a,a)]
pairs (x:y:ls) = (x,y):pairs ls

-- From the pairs of random numbers, get the proportion of points inside the 
-- circle and use to get pi.
montePi' :: Double
montePi' = 4 * hits src / fromIntegral samples
  where
    samples = 10000
    hits    = fromIntegral . 
              length . 
              filter (uncurry inside) . 
              take samples . 
              pairs
    src     = randomRs (0, 1) (mkStdGen 42) :: [Double]