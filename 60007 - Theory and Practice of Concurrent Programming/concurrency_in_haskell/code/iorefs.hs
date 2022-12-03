import Control.Concurrent (MVar, takeMVar, newEmptyMVar, putMVar, forkIO)
import Control.Monad (replicateM, zipWithM_)
import Data.IORef ( IORef, atomicModifyIORef, newIORef, readIORef )

increment :: MVar () -> IORef Integer -> Integer -> IO ()
increment h i t = do
    (oldval, newval) <- atomicModifyIORef i (\v -> (v + 1, (v, v+1)))
    putStrLn $ "Thread " ++ show t ++ " is incremenbted value from " ++ show oldval ++ " to " ++ show newval
    putMVar h ()

main :: IO ()
main = do
    mvars   <- replicateM 10 newEmptyMVar
    counter <- newIORef 0
    zipWithM_ (\ x y -> forkIO (increment x counter y)) mvars [1..]
    mapM_ takeMVar mvars
    finalValue <- readIORef counter
    putStrLn $ "Final value is: " ++ show finalValue
