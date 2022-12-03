import Control.Concurrent ( forkIO, newEmptyMVar, putMVar, takeMVar, MVar )

childThread :: MVar String -> IO ()
childThread m = do
    let msg = "Hello notes reader!"
    putStrLn $ "Determining the message as: " ++ msg
    putMVar m msg

main :: IO ()
main = do
    msgVar <- newEmptyMVar
    forkIO $ childThread msgVar
    msg <- takeMVar msgVar
    putStrLn $ "Got the message: " ++ msg
