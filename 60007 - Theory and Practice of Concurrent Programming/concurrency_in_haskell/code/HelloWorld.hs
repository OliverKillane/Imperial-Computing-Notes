import Control.Concurrent (MVar, takeMVar, newEmptyMVar, putMVar, forkIO)
import Control.Monad (replicateM, zipWithM)


printHello :: MVar () -> Integer -> IO ()
printHello h i = do
    -- print out the message
    putStrLn ("This is thread " ++ show i ++ " saying hello world!")

    -- place a value in the mutable variable
    putMVar h ()

main :: IO ()
main = do
    -- create the mutable variables
    mvars <- replicateM 10 newEmptyMVar

    -- for each mutable variable fork off a process with it & the index
    res <- zipWithM (\ x y -> forkIO (printHello x y)) mvars [1..]

    -- for each mutable variable, attempt to get the value (will wait until a value is put)
    mapM_ takeMVar mvars
