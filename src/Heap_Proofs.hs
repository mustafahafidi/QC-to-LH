{- 
=================================================================
                QuickCheck's Heap Example proofs
=================================================================
-}
module Heap_Proofs where



import Lib.LH.Prelude
-- import Lib.LH.Equational
import Lib.QC.Heap -- hiding ( (==?))
import Language.Haskell.Liquid.ProofCombinators
-- import Language.Haskell.Liquid.Prelude
import Prelude hiding (length, null, splitAt, (++), reverse)

{-@ LIQUID "--reflection"    @-}
-- {-@ LIQUID "--no-totality"    @-}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--higherorder"    @-}


{-@ prop_Empty :: { Lib.QC.Heap.prop_Empty } @-}
prop_Empty :: Proof
prop_Empty =
  (empty ==? ([]::[Int]))
  === (Empty ==? ([]::[Int]))
  === (invariant (Empty::Heap Int) && sort (toList Empty) == sort ([]::[Int]))
  === (True && sort (toList Empty) == sort ([]::[Int]))
  === (sort (toList Empty) == sort ([]::[Int]))
  === (sort (toList' [Empty]) == sort ([]::[Int]))
  === (sort (toList' []) == sort ([]::[Int]))
  === (sort ([]) == sort ([]::[Int]))
  === (([]) == ([]::[Int]))
   ***QED

{-@ prop_IsEmpty ::  h:Heap Int -> { Lib.QC.Heap.prop_IsEmpty h } @-}
prop_IsEmpty ::  Heap Int -> Proof
prop_IsEmpty h@Empty =  
        (isEmpty h == null (toList h))
        === (True == null (toList h))
        === (null (toList h))
        === (null (toList' [h]))
        === (null (toList' []))
        === (null [])
        ***QED 

prop_IsEmpty h@(Node v hl hr) =  
        (isEmpty h == null (toList h))
        === (False == null (toList h))
        === (False == null (toList' [h]))
        === (False == null (v: (toList' (hl:hr:[]))))
        === (False == null (v: (toList' (hl:hr:[])))) -- lazy evaluation helps to prove
        ***QED


