import Control.Monad.Random (getRandom)

main :: IO ()
main = do
    x <- getRandom :: IO Int
    print (42 + x)