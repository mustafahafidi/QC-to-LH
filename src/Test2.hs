-- import Lib.QC.Heap (merge, Heap(..))
-- import Prelude hiding (minimum)
import Language.Haskell.Liquid.ProofCombinators hiding ((==.))
-- import Test_Heap
import Lib.LH.Prelude
import Lib.QC.Heap (unit, empty, (==?),  toList,toList', invariant, Heap(..), (<=?))
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}


{-@ inline ppp @-}
ppp x = unit x ==? [x]
{-@ ple foo @-}
{-@ foo ::  x:Int -> { ppp x } @-}
foo ::  Int -> Proof
foo x = trivial