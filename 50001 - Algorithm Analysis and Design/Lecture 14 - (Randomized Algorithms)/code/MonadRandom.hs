class Monad m => MonadRandom m where
  getRandom   :: Random a => m a
  getRandoms  :: Random a => m [a]
  getRandomR  :: Random a => (a, a) -> m a
  getRandomRs :: Random a => (a, a) -> m [a]