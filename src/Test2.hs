module Test2 where
import Lib.LH.Prelude 
import Prelude hiding (any)
import Lib.CL.CircularList
import Language.Haskell.Liquid.ProofCombinators
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}


{-@ reflect =*= @-}
{-@ infix 4 =*= @-}
(=*=) :: Eq a  => CList a -> CList a -> Bool
a =*= b =  (any (\x->(toList a == toList x)) . toList $ allRotations b)
