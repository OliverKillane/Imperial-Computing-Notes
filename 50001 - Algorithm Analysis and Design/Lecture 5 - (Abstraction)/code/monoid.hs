class Monoid m where
    (<>) :: m -> m -> m
    mempty :: m
