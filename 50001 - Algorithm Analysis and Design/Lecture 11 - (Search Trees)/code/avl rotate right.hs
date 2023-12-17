rotr :: HTree a -> HTree a
rotr (HNode _ (HNode _ ll x lr) y r) = hnode ll x (hnode lr y r)