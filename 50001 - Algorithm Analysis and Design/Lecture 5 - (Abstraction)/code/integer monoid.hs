-- declaring newtype so that many monoid instance on Int do not conflict
newtype PlusInt = PlusInt Int

instance Monoid PlusInt where
    (<>) :: PlusInt -> PlusInt -> PlusInt
    (<>) = (+)

    mempty :: PlusInt 
    mempty = 0
