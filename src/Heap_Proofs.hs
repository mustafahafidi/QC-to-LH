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



{-======================================================
                        prop_Empty
=======================================================-}
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


{-======================================================
                        prop_IsEmpty
=======================================================-}
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



{-======================================================
                        prop_Unit
=======================================================-}
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
                -- def. of invariant
                === (x <=? Empty && x <=? Empty && invariant (Empty::Heap Int) && invariant (Empty::Heap Int))
            --  === (True && True && True && True)
            ***QED



{-======================================================
                        prop_Size
=======================================================-}
{-@ inline disToList @-}
disToList h1 h2 = toList' (h1++h2) == (toList' h1 ++ toList' h2)

{-@ distProp ::  Eq a =>  h1:[Heap a] -> h2:[Heap a] -> { disToList h1 h2 } @-}
distProp :: Eq a => [Heap a] -> [Heap a] -> Proof
distProp (h:hs) h2 =    (toList' ((h:hs)++h2) == (toList' (h:hs) ++ toList' h2))
                        ? (      (h:hs) ++ h2
                              === (h:hs) ++ h2
                              === h:([]++hs) ++ h2
                              === ([h]++hs) ++ h2
                                     ? assocP [h] hs h2
                              === [h]++(hs++h2)
                          )
                        === (toList' ([h]++(hs++h2)) == (toList' (h:hs) ++ toList' h2))
                              -- expand left handside
                        ? (   toList' ([h]++(hs++h2))
                                    ? distProp [h] (hs++h2)
                          === toList' [h] ++ toList' (hs++h2)  
                                    ? distProp hs h2
                          === toList' [h] ++ (toList' hs ++ toList' h2) 
                                    ? assocP (toList' [h]) (toList' hs ) (toList' h2)
                          === (toList' [h] ++ toList' hs) ++ toList' h2 
                                    ? distProp [h] hs
                          === toList' ([h] ++ hs) ++ toList' h2
                          === toList' (h:hs) ++ toList' h2
                          )
                        === (toList' (h:hs) ++ toList' h2 == toList' (h:hs) ++ toList' h2)
                        ***QED

{- 
distProp (h:hs) h2 =  (toList' ((h:hs)++h2) == (toList' (h:hs) ++ toList' h2))
                              ? distProp (h:hs) (h2)
                        ***QED  -}

{-@ prop_Size ::  h:Heap Int -> { Lib.QC.Heap.prop_Size h } @-}
prop_Size ::  Heap Int -> Proof
prop_Size Empty =  (size Empty == length (toList Empty))
                  ===  ( 0 == length (toList' [Empty]))
                  ===  ( 0 == length (toList' []))
                  ===  ( 0 == length [])
                  ***QED

prop_Size h@(Node v hl hr) =  (size h == length (toList h)) -- apply size
            ===  (1 + size hl + size hr == length (toList' [h]))  -- apply toList'
            ===  (1 + size hl + size hr == length (v:toList' [hl,hr])) ? (    [hl]++[hr]
                                                                          === hl:([]++[hr])
                                                                          === hl:[hr] )
            === (1 + size hl + size hr == length (v:toList' ([hl]++[hr]))) -- distributivity of toList'
                  ? distProp [hl] [hr]
            ===  (1 + size hl + size hr == length (v:(toList' [hl] ++ toList' [hr]))) -- def of length
            ===  (1 + size hl + size hr == 1 + length (toList' [hl] ++ toList' [hr])) -- mult. length
            ===  (1 + size hl + size hr == 1 + length (toList' [hl]) + length (toList' [hr])) -- toList' to toList
            === (1 + size hl + size hr == 1 + length (toList hl) + length (toList hr))
                  ? Heap_Proofs.prop_Size hl
                  ? Heap_Proofs.prop_Size hr
            === (size h == length (toList h)) 
            ***QED



{-======================================================
                        prop_Insert
=======================================================-}

{-@ lemma_invariant :: Ord a =>  h1:{ Heap a | Lib.QC.Heap.invariant h1 }
                      -> h2:{ Heap a | Lib.QC.Heap.invariant h2 } 
                      -> { Lib.QC.Heap.invariant (merge h1 h2) } @-}
lemma_invariant ::  Ord a => Heap a -> Heap a -> Proof
lemma_invariant h1 h2 = invariant (merge h1 h2)
                    ***QED
                    
{-@ prop_Insert ::  x:Int -> hp:Heap Int -> { Lib.QC.Heap.prop_Insert x hp } @-}
prop_Insert ::  Int -> Heap Int -> Proof
prop_Insert x Empty =   ( insert x Empty ==? (x : toList Empty) )
                ===  ( unit x `merge` Empty ==? (x : toList' [Empty]) )
                ===  ( (Node x empty empty) `merge` Empty ==? (x : toList' [Empty]) )
                ===  ( Node x empty empty ==? (x : toList' [Empty]) )
                ===  ( Node x empty empty ==? (x : toList' []) )
                ===  ( Node x empty empty ==? [x])
                ===  ( Node x Empty Empty ==? [x])
                ===  ( invariant (Node x Empty Empty) && sort (toList (Node x Empty Empty)) == sort [x])
                  -- Def. of invariant
                ===  ( let inv = (x <=? Empty && x <=? Empty && invariant (Empty::Heap Int) && invariant (Empty::Heap Int))
                               === (x <=? Empty)
                               === True
                        in inv && sort (toList (Node x Empty Empty)) == sort [x])
                ===  (sort (toList (Node x Empty Empty)) == sort [x])
                ===  (sort (toList' [Node x Empty Empty]) == sort [x])
                ===  (sort (x:toList' [Empty,Empty]) == sort [x])
                ===  (sort (x:toList' []) == sort [x])
                ===  (sort [x] == sort [x])
                ***QED

prop_Insert x h@(Node y hl hr) 
            | x <= y    =    ( insert x h ==? (x : toList h) )
                        ===  ( unit x `merge` h ==? (x : toList' [h]) )
                        ===  ( unit x `merge` h ==? (x : y : toList' [hl,hr]) )
                        ===  ( (Node x empty empty) `merge` h ==? (x : y : toList' [hl,hr]) )
                        ===  ( (Node x Empty Empty) `merge` h ==? (x : y : toList' [hl,hr]) )
                        ===  ( Node x (Empty `merge` h) Empty ==? (x : y : toList' [hl,hr]) )
                        ===  ( Node x h Empty ==? (x : y : toList' [hl,hr]) )
                        ===  ( Node x h Empty ==? (x : y : toList' [hl,hr]) )
                        === (invariant (Node x h Empty) && sort (toList (Node x h Empty)) == sort (x : y : toList' [hl,hr]))
                                                               ? ( (toList (Node x h Empty))
                                                             === (toList' [Node x h Empty])
                                                             === (x: toList' [h,Empty])
                                                             === (x: y: toList' [hl,hr,Empty])
                                                             ==! (x: y: toList' ([hl,hr]++[Empty]))
                                                                        ? disToList [hl,hr] [Empty]
                                                             ==! (x: y: ((toList' [hl,hr])++ (toList'[Empty])))
                                                             === (x: y: ((toList' [hl,hr])++ (toList'[])))
                                                             ==! (x: y: ((toList' [hl,hr])++ []))
                                                             ==! (x: y: (toList' [hl,hr])) )
                        === (invariant (Node x h Empty) && sort (x: y: (toList' [hl,hr])) == sort (x : y : toList' [hl,hr]))
                        === (invariant (Node x h Empty))
                        === (x <=? h && x <=? Empty && invariant h && invariant (Empty::Heap Int)) --def of <=? and invariant
                              -- ? invariant h
                              -- ? lemma_invariant x h
                        === (x <= y && invariant h)
                              ? invariant h
                        === True
                        -- === (invariant ( x <=? hl && x <=? hr && invariant hl && invariant hr ))
                        ***QED                                               

            | otherwise = True
                  -- Node y (h22 `merge` h1) h21

                ***Admit
 