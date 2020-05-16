{- 
=================================================================
                QuickCheck's Heap Example proofs
=================================================================
-}
module Heap_Proofs where



import Lib.LH.Prelude
-- import Lib.LH.Equational
import Lib.QC.Heap -- hiding ( (==?))
-- import Lib.QC.ExtraTheorems
import Language.Haskell.Liquid.ProofCombinators
-- import Language.Haskell.Liquid.Prelude
import Prelude hiding (length, null, splitAt, (++), reverse)

{-@ LIQUID "--reflection"    @-}
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
------ Distributivity of toList' over (++)
{-@ inline disToList @-}
disToList h1 h2 = toList' (h1++h2) == (toList' h1 ++ toList' h2)
{-@ distProp ::  Eq a =>  h1:[Heap a] -> h2:[Heap a] -> { disToList h1 h2 } @-}
distProp :: Eq a => [Heap a] -> [Heap a] -> Proof
distProp [] h2 = ( toList' ([]++h2) == (toList' [] ++ toList' h2) )
                                    ?  (toList' [] ++ toList' h2
                                       === [] ++ toList' h2
                                       === toList' h2
                                       )
             === ( toList' h2 == toList' h2 )
                  ***QED

distProp ((h@Empty):hs) h2 = (toList' ((h:hs)++h2) == (toList' (h:hs) ++ toList' h2))
                    ?(
                        toList' ((h:hs)++h2)
                    === toList' (h:(hs++h2))
                    === toList' (hs++h2)
                    )
                                                ?(toList' (h:hs)
                                                === toList' hs
                                                )
                    === (toList' (hs++h2) == toList' hs ++ toList' h2)
                       ? distProp hs h2 
                      
                 ***QED

distProp (h@(Node x hl hr):hs) h2 =  
            (toList' ((h:hs)++h2) == (toList' (h:hs) ++ toList' h2))
            ?(
                toList' ((h:hs)++h2)
            === toList' (h:(hs++h2))
                ? (  toList' (h:(hs++h2))
                 ==! toList' [h] ++ toList' (hs++h2))
            === toList' [h] ++ toList' (hs++h2)
                ? distProp hs h2
            === toList' [h] ++ (toList' hs ++ toList' h2)
                ? assocP (toList' [h]) (toList' hs) (toList' h2)
            === (toList' [h] ++ toList' hs) ++ toList' h2
                ? (  toList' (h:hs)
                 ==! toList' [h] ++ toList' hs)
                 
            === toList' (h:hs) ++ toList' h2
            )
            ***QED


{-@ inline lemma_distProp_p @-}
lemma_distProp_p h hs = toList' (h:hs) == toList' [h] ++ toList' hs
{-@ lemma_distProp :: Eq a => h:Heap a -> hs:[Heap a] -> { lemma_distProp_p h hs } @-}
lemma_distProp :: Eq a => Heap a -> [Heap a] -> Proof
lemma_distProp h@Empty hs =  toList' [h] ++ toList' hs
                    ? (
                        toList' [h]
                    === toList' []
                    === []
                    )
                === [] ++ toList' hs
                === toList' hs
                === toList' (h:hs) 
                ***QED
lemma_distProp h@(Node x hl hr) hs = toList' (h:hs)
                        === x: toList' (hl:hr:hs)
                            ? lemma_distProp hl (hr:hs)
                        === x: (toList' [hl] ++ toList' (hr:hs))
                                                ? lemma_distProp hr hs
                        === x: (toList' [hl] ++ (toList' [hr] ++ toList' hs))
                                ? assocP (toList' [hl]) (toList' [hr]) (toList' hs)
                        === x: ((toList' [hl] ++ toList' [hr]) ++ toList' hs)
                            ? lemma_distProp hl [hr]
                        === x: ((toList' (hl:[hr])) ++ toList' hs)
                        === x: toList' (hl:hr:[]) ++ toList' hs
                        === (x: toList' (hl:hr:[])) ++ toList' hs
                        === (toList' ([h])) ++ toList' hs
                ***QED
------ End Distributivity of toList' over (++)


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

{-@ prop_Insert ::  x:Int -> hp:Heap Int -> { Lib.QC.Heap.prop_Insert x hp } @-}
prop_Insert ::  Int -> Heap Int -> Proof
prop_Insert x Empty =   ( insert x Empty ==? (x : toList Empty) )
                                            ? (
                                                (x : toList' [Empty])
                                            === x : toList' []
                                            === [x]
                                            )
                    ===  ( insert x Empty ==? [x])
                    === (let h = insert x Empty
                        in (invariant h && sort (toList h) == sort [x])
                        )
                    === (sort (toList (insert x Empty)) == sort [x])
                             ?(
                                (toList (insert x Empty))
                            === (toList ( unit x `merge` Empty))
                            === (toList ( (Node x empty empty) `merge` Empty))
                            === (toList (Node x empty empty))
                            === (toList' [Node x Empty Empty])
                            === (x : toList' (Empty:Empty:[]))
                            === (x : toList' (Empty:[]))
                            === (x : toList' ([]))
                            === ([x]) 
                             )
                ***QED 

prop_Insert x h@(Node y hl hr)
            | x <= y    = let h= (Node y hl hr)
                        in (insert x h ==? (x : toList h))
                            ? (insert x h ==! Node x (Node y hl hr) Empty)
                                                ? (x:toList h  ==! (x : y : toList' [hl,hr]))
                        ===  ((Node x h Empty) ==? (x : y : toList' [hl,hr]))
                        === (invariant (Node x h Empty) 
                                && sort (toList (Node x h Empty)) == sort (x : y : toList' [hl,hr]))
                        === sort (toList (Node x h Empty)) == sort (x : y : toList' [hl,hr])
                                ?(
                                  toList (Node x h Empty)
                                === toList' ([Node x h Empty])
                                === x:toList' ([h,Empty])
                                === x:y:toList' ([hl,hr,Empty])
                                                ?( [hl,hr,Empty]
                                                === hl:hr:[Empty]
                                                === hl:hr:([]++[Empty])
                                                === hl:([hr]++[Empty])
                                                === [hl,hr]++[Empty]
                                                )
                                    ? distProp [hl,hr]  [Empty]
                                === x:y:( toList' [hl,hr] ++ toList' [Empty] )
                                                            ?(
                                                                toList' [Empty]
                                                            === toList' []
                                                            === []
                                                            )
                                                            ?rightIdP (toList' [hl,hr])
                                === x:y:( toList' [hl,hr] )
                                )
                        ***QED
 
            | otherwise = let h = (Node y hl hr)
                        in (insert x h ==? (x : toList h))
                            ? (insert x h 
                             === (unit x) `merge` h
                             === (Node x empty empty) `merge` h
                             === ((Node x Empty Empty) `merge` (Node y hl hr))
                            --  === (Node y (hr `merge` (Node x Empty Empty)) hl)
                             )
                            
                                ? ( toList' [Node x empty empty, h]
                                === x: toList' [empty,empty,h]
                                === x: toList' [empty,h]
                                === x: toList' [h]
                                === x: toList h
                                )
                                ? lemma_sort_merge (Node x empty empty) h
                            === (Node x empty empty) `merge` h ==? toList' [Node x empty empty, h]
                        
                ***QED


{-======================================================================================
                        LEMMAS AND THEOREMS
========================================================================================-}

{-@ inline lemma_sort_merge_p @-}
lemma_sort_merge_p hl hr = (hl `merge` hr) ==? toList' [hl,hr]
{-@ lemma_sort_merge :: Ord a =>  hl:Heap a ->  hr:Heap a -> { lemma_sort_merge_p hl hr } @-}
lemma_sort_merge :: Ord a => Heap a ->  Heap a -> Proof
lemma_sort_merge hl@Empty hr  = (hl `merge` hr) ==? toList' [hl,hr]
                            === hr ==? toList' [hr]
                            === (invariant hr && sort (toList hr) == sort (toList' [hr]))
                            === sort (toList hr) == sort (toList' [hr])
                            === sort (toList' [hr]) == sort (toList' [hr])
                            ***QED

lemma_sort_merge hl hr =
                            (hl `merge` hr) ==? toList' [hl,hr]
                            === (invariant (hl `merge` hr) && sort (toList (hl `merge` hr)) == sort (toList' [hl,hr]))
                            === sort (toList (hl `merge` hr)) == sort (toList' [hl,hr])
                                    ?(sort (toList (hl `merge` hr))
                                    ==! sort (toList hl ++ toList hr)
                                    === sort (toList' [hl] ++ toList' [hr])
                                            ? lemma_distProp hl [hr]
                                    === sort (toList' [hl,hr])
                                    )
                            ***QED



-------------
{-@ inline  th_sort_arg_rev_p @-}
th_sort_arg_rev_p ls rs = sort (ls++rs) == sort (rs++ls)

{-@ th_sort_arg_rev :: Ord a =>  ls:[a] -> rs:[a] -> {  th_sort_arg_rev_p ls rs } @-}
th_sort_arg_rev ls rs =  sort (ls++rs)  ==! sort (rs++ls)
                            ***Admit
-------------
{-@ inline  th_sort_arg_app_p @-}
th_sort_arg_app_p ls rs = sort (ls++rs) == sort (sort ls++rs)

{-@ th_sort_arg_app :: Ord a =>  ls:[a] -> rs:[a] -> {  th_sort_arg_app_p ls rs } @-}
th_sort_arg_app ls rs =  sort (ls++rs)  ==! sort (sort ls++rs)
                            ***Admit
-------------
{-@ inline  th_sort_arg_cons_p @-}
th_sort_arg_cons_p l rs = sort (l:rs) == sort (l:sort rs)

{-@ th_sort_arg_cons :: Ord a =>  l:a -> rs:[a] -> {  th_sort_arg_cons_p l rs } @-}
th_sort_arg_cons l rs =  sort (l:rs) == sort (l:sort rs)
                            ***Admit
-------------


{-@ LIQUID "--nototality" @-}
{-@ inline  theorem_sort_tolist_merge_p @-}
theorem_sort_tolist_merge_p hl hr = sort (toList (hl `merge` hr)) == sort (toList hl ++ toList hr)

{-@ theorem_sort_tolist :: Ord a =>  hl:Heap a -> hr:Heap a -> {  theorem_sort_tolist_merge_p hl hr } @-}
theorem_sort_tolist :: Ord a =>  Heap a -> Heap a -> Proof
theorem_sort_tolist  hl@Empty hr = sort (toList (hl `merge` hr)) == sort (toList hl ++ toList hr)
                                    ?(
                                    sort (toList (hl `merge` hr))
                                === sort (toList hr)
                                    )
                                                                    ?(
                                                                    sort (toList hl ++ toList hr)
                                                                === sort (toList' [hl] ++ toList hr)
                                                                === sort (toList' [] ++ toList hr)
                                                                === sort ([] ++ toList hr)
                                                                === sort (toList hr)
                                                                    )
                                ***QED
theorem_sort_tolist  hl@(Node x h11 h12) hr@(Node y h21 h22) 
                | x<=y    = let hl=Node x h11 h12
                                hr=Node y h21 h22
                            in sort (toList (hl `merge` hr)) == sort (toList hl ++ toList hr)
                                ?(sort (toList (hl `merge` hr))
                                === sort (toList' [hl `merge` hr])
                                === sort (toList' [Node x (h12 `merge` hr) h11])
                                === sort (x:toList' [(h12 `merge` hr),h11])
                                === sort (x:([] ++ toList' [(h12 `merge` hr),h11]))
                                === sort ([x] ++ toList' [(h12 `merge` hr),h11])
                                        ? th_sort_arg_rev [x] (toList' [(h12 `merge` hr),h11]) --reverse the ops of ++

                                === sort ((toList' [(h12 `merge` hr),h11]) ++ [x])
                                        ? th_sort_arg_app (toList' [(h12 `merge` hr),h11]) [x]
                                === sort (sort (toList' [(h12 `merge` hr),h11]) ++ [x])
                                        ? th_sort_arg_rev (sort (toList' [(h12 `merge` hr),h11])) [x]
                                === sort ([x] ++ sort (toList' [(h12 `merge` hr),h11]))
                                         ?(
                                            [x] ++ sort (toList' [(h12 `merge` hr),h11])
                                        === x: ([] ++ sort (toList' [(h12 `merge` hr),h11]))
                                        === x: (sort (toList' [(h12 `merge` hr),h11]))
                                         )
                                === sort (x:sort (toList' [(h12 `merge` hr),h11]))
                                            ?(x:sort (toList' [(h12 `merge` hr),h11])
                                                  ? lemma_distProp (h12 `merge` hr) [h11]
                                            === (x:sort (toList' [(h12 `merge` hr)] ++ toList' [h11]))
                                                ? th_sort_arg_app (toList' [(h12 `merge` hr)]) (toList' [h11])
                                            ===(x:sort (sort (toList' [(h12 `merge` hr)]) ++ toList' [h11]))
                                            ===(x:sort (sort (toList (h12 `merge` hr)) ++ toList' [h11]))
                                            )
                                            ?((sort (toList (h12 `merge` hr)))
                                                ? theorem_sort_tolist h12 hr
                                            === sort (toList h12 ++ toList hr)
                                            )
                            --
                                === sort (x:sort ( sort (toList h12 ++ toList hr) ++ toList' [h11]))
                                                ? th_sort_arg_app (toList h12 ++ toList hr) (toList' [h11])

                                === sort (x:sort ((toList h12 ++ toList hr) ++ toList' [h11]))
                                                    ? th_sort_arg_rev (toList h12 ++ toList hr) (toList' [h11])

                                === sort (x:sort (toList' [h11] ++ (toList h12 ++ toList hr)))
                                        ?((toList' [h11] ++ (toList h12 ++ toList hr))
                                            ? assocP (toList' [h11]) (toList h12 ) (toList hr)
                                         === ((toList' [h11] ++ toList h12) ++ toList hr)
                                         === ((toList' [h11] ++ toList' [h12]) ++ toList hr)
                                                ? lemma_distProp h11 [h12]
                                         === (toList' [h11,h12] ++ toList hr)
                                         === (toList' [h11,h12] ++ toList' [hr])
                                                ? distProp [h11,h12] [hr]
                                        === (toList' ([h11,h12] ++ [hr]))
                                                    ?(([h11,h12] ++ [hr])
                                                    === h11:([h12] ++ [hr])
                                                    === h11:h12:([] ++ [hr])
                                                    === h11:h12:([hr])
                                                    )
                                        === (toList' [h11,h12,hr])
                                        )
                                        ? th_sort_arg_cons x (toList' [h11,h12,hr])
                                ===  sort (x:(toList' [h11,h12,hr]))
                                === sort (toList' [(Node x h11 h12),hr])
                                === sort (toList' [hl,hr])
                                        ? lemma_distProp hl [hr]
                                === sort (toList' [hl] ++ toList' [hr])
                                === sort (toList hl ++ toList hr)
                                )
                         ***Admit
