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
{-@ LIQUID "--no-totality"    @-}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination"    @-}


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
        === not (null (toList' [h]))
        === not (null (v: (toList' (hl:hr:[]))))
        === not (null (v: (toList' (hl:hr:[])))) 
        ***QED


{-@ prop_Unit ::  x:Int -> { Lib.QC.Heap.prop_Unit x } @-}
prop_Unit ::  Int -> Proof
prop_Unit x = (unit x ==? [x])
            === -- definition of ==?
              (let h = Node x empty empty in 
                    (invariant h && sort (toList h) == sort [x])
                === (invariant h && sort (toList h) == sort [x])
                === (invariant h && sort (toList' [h]) == sort [x])
                === (invariant h && sort (x:toList' (Empty:Empty:[])) == sort [x])
                === (invariant h && sort (x:toList' (Empty:Empty:[])) == sort [x])
                === (invariant h && sort (x:toList' (Empty:[])) == sort [x])
                === (invariant h && sort (x:toList' []) == sort [x])
                === (invariant h && sort [x] == sort [x])
                === (invariant h)) 
                === (let e = (Empty::Heap Int) in -- definition of invariant
                      (x <=? Empty && x <=? Empty && invariant e && invariant e))
            --  === (True && True && True && True)
            ***QED



{-@ inline dsp @-}
dsp h1 h2 = toList' (h1++h2) == (toList' h1 ++ toList' h2)


{-@ distProp ::  Eq a =>  h1:[Heap a] -> h2:[Heap a] -> { dsp h1 h2 } @-}
distProp :: Eq a => [Heap a] -> [Heap a] -> Proof
distProp h1@(h:hs) h2 =  (toList' ((h:hs)++h2) == (toList' (h:hs) ++ toList' h2))
                              ? distProp (h:hs) (h2)
                        -- === (toList' (h:hs) ++ toList' h2 == toList' (h:hs) ++ toList' h2)
                        ***QED

{-@ prop_Size ::  h:Heap Int -> { Lib.QC.Heap.prop_Size h } @-}
prop_Size ::  Heap Int -> Proof
prop_Size Empty =  (size Empty == length (toList Empty))
                  ===  ( 0 == length (toList' [Empty]))
                  ===  ( 0 == length (toList' []))
                  ===  ( 0 == length [])
                  ***QED

prop_Size h@(Node v hl hr) =  (size h == length (toList h))
            ===  (1 + size hl + size hr == length (toList' [h]))
            ===  (1 + size hl + size hr == length (v:toList' [hl,hr])) ? ([hl]++[hr]===hl:([]++[hr])===hl:[hr])
            === (1 + size hl + size hr == length (v:toList' ([hl]++[hr]))) -- distAppend of toList'
                  ? distProp [hl] [hr]
            ===  (1 + size hl + size hr == length (v:(toList' [hl] ++ toList' [hr]))) 
            ===  (1 + size hl + size hr == 1 + length (toList' [hl] ++ toList' [hr]))
            ===  (1 + size hl + size hr == 1 + length (toList' [hl]) + length (toList' [hr]))
            === (1 + size hl + size hr == 1 + length (toList hl) + length (toList hr))
                  ? Heap_Proofs.prop_Size hl
                  ? Heap_Proofs.prop_Size hr
            === (size h == length (toList h)) 
            ***QED