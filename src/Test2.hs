module Test2 where
import Lib.LH.Prelude 
import Prelude hiding (any, reverse, (++))
import Lib.CL.CircularList
import Language.Haskell.Liquid.ProofCombinators
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--short-names" @-}


asd :: Proof
asd =  (reverse ( ([1]) ++ ([1,2])))
        ? (distributivityP ([1]) ([1,2]) ***Admit)
   === ((reverse [1]) ++ (reverse [1,2]))
   ***QED