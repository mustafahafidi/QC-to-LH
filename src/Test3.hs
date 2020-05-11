module Test3 where
{-@ LIQUID "--reflection"    @-}



{-@ reflect foo @-}
{-@ foo :: Maybe {v:Int | v == 4 }  @-}
foo :: Maybe Int
foo = Just $ (1+1)

{-@ reflect bar @-}
bar :: a ->  a -> Maybe Int
bar _ _ = Just (1+1)
