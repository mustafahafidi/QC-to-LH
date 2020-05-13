module Lib.CL.ExtraTheorems where
import Language.Haskell.Liquid.Prelude
import Prelude  hiding (length, 
                        (++), 
                        reverse, 
                        iterate, 
                        null, 
                        splitAt,
                        any
                        )
import Lib.LH.Prelude 
import Lib.CL.CircularList
-- import qualified CList_Proofs as CLP
import Language.Haskell.Liquid.ProofCombinators

{-@ LIQUID "--reflection"    @-}
{-@ LIQUID "--short-names"    @-}
-- {-@ LIQUID "--ple"    @-}


{-@ reflect =*= @-}
{-@ infix 4 =*= @-}
(=*=) :: Eq a  => CList a -> CList a -> Bool
a =*= b = (any ((toList a ==) . toList) . toList $ allRotations b)

{- 

{-@ inline lemma_any_p @-}
lemma_any_p p ls rs = any p (ls++rs) == ((any p ls) || (any p rs))
{-@ lemma_any :: p:(a->Bool) -> ls:[a] -> rs:[a] -> { lemma_any_p p ls rs } @-}
lemma_any :: (a->Bool) -> [a] -> [a] -> Proof
lemma_any p [] rs = ( any p ([]++rs))
                === ( any p rs)
                === ( any p [] || any p rs)
                ***QED

lemma_any p (l:ls) rs = ( any p ((l:ls)++rs))
                    === ( any p (l:(ls++rs)))
                    === ( p l || any p (ls++rs))
                                    ? lemma_any p ls rs
                    === ( p l || (any p ls) || (any p rs))
                    === ( (any p (l:ls)) || (any p rs))
                    ***QED -}