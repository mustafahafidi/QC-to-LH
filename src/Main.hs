module Main where
import Lib.LH.Prelude
import Lib.LH.Equational
import Lib.CL.CircularList
import Prelude hiding (length)
-- import Lib.CL.QuickCheck (prop_empty)
import Data.Typeable
-- import Language.Haskell
-- import Language.Haskell.Liquid.Prelude (plus)
-- import Language.Haskell.Liquid.ProofCombinators


{-@ LIQUID "--reflection"    @-}



-- {-@ assume Lib.CL.CircularList.toList :: CList a -> {xs:[a] | (length xs) >= 0} @-}
-- {-@ assume Lib.CL.CircularList.toInfList :: CList a -> {xs:[a] | (length xs) >= 0} @-}
-- {-@ reflect toList @-}
{- -- {-@ reflect toList @-}
{-@ prop_empty :: { length (toList empty) = 0} @-}
prop_empty :: Proof
prop_empty = length (toList empty) == 0
             ***QED -}


{-@ prop_empty :: { c == (fromList . toList $ c) } @-}
prop_list :: CList Int -> Proof
prop_list c = c == (fromList . toList $ c)
            ***QED

{- 
{-@ prop_empty :: {  (Just v) == (focus $ insertR v c) } @-}
prop_focus :: CList Int -> Int -> Proof
prop_focus c v = (Just v) == (focus $ insertR v c)
                 ***QED
 -}
 




main :: IO ()
main = putStrLn (show $ "Hello world")
