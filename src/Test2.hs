-- import Lib.QC.Heap (merge, Heap(..))
import Prelude hiding (minimum)
import Language.Haskell.Liquid.ProofCombinators hiding ((==.))
import Test_Heap
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}

{-@ test :: OList Int @-}
test :: [Int]
test = [1,2,3]