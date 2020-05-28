module Lib.QC.ExtraTheorems where
import Lib.LH.Prelude ((++), reverse, sort, insertSort, assocP)
import Prelude hiding ((++), reverse)
import Language.Haskell.Liquid.ProofCombinators
import Lib.QC.Heap
-- import Heap_Proofs
{-@ LIQUID "--reflection"    @-}
{-@ LIQUID "--shortnames" @-}
