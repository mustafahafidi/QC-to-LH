import Test2
import Language.Haskell.Liquid.ProofCombinators
import Lib.CL.CircularList
import Prelude hiding (any)
{-@ LIQUID "--reflection" @-}

{-@ bar ::  Proof @-}
bar ::  Proof
bar =  Empty =*= (Empty::CList Int)
    ***QED