rotl :: HTree a -> HTree a
rotl (HNode _ ll w (HNode _ lrl x lrr))
  = hnode (hnode ll w lrl) x lrr

-- so for the example: HNode _ wt y r -> rotr ( hnode (rotl wt) y r)