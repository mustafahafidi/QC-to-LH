module Test2 where
    

{-@ reflect foo @-}
{-@ foo :: Maybe {v:Int | v == 4 }  @-}
foo :: Maybe Int
foo = Just $ 1+1