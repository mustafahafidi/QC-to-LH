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
import Prelude hiding (length, null, splitAt, (++), reverse, Maybe (..), minimum)


{-@ LIQUID "--reflection"    @-}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--ple-local" @-}


{-======================================================
                        prop_Empty
=======================================================-}
{-@ ple prop_Empty @-}
{-@ prop_Empty :: { Lib.QC.Heap.prop_Empty } @-}
prop_Empty :: Proof
prop_Empty = ()
    --   (empty ==? ([]::[Int]))
--   === (Empty ==? ([]::[Int]))
--   === (invariant (Empty::Heap Int) && sort (toList Empty) == sort ([]::[Int]))
--   === (True && sort (toList Empty) == sort ([]::[Int]))
--   === (sort (toList Empty) == sort ([]::[Int]))
--   === (sort (toList' [Empty]) == sort ([]::[Int]))
--   === (sort (toList' []) == sort ([]::[Int]))
--   === (sort ([]) == sort ([]::[Int]))
--   === (([]) == ([]::[Int]))
--    ***QED


{-======================================================
                        prop_IsEmpty
=======================================================-}
{-@ ple prop_IsEmpty @-}
{-@ prop_IsEmpty ::  h:Heap Int -> { Lib.QC.Heap.prop_IsEmpty h } @-}
prop_IsEmpty ::  Heap Int -> Proof
prop_IsEmpty h@Empty =  trivial
        -- (isEmpty h == null (toList h))
        -- -- === (True == null (toList h))
        -- -- === (null (toList h))
        -- -- === (null (toList' [h]))
        -- -- === (null (toList' []))
        -- -- === (null [])
        -- ***QED 

prop_IsEmpty h@(Node v hl hr) =  trivial
        -- (isEmpty h == null (toList h))
        -- -- === (False == null (toList h))
        -- -- === not (null (toList' [h]))
        -- -- === not (null (v: (toList' (hl:hr:[]))))
        -- -- === not (null (v: (toList' (hl:hr:[])))) 
        -- ***QED

-- {-======================================================
--                         prop_Unit
-- =======================================================-}
{-@ ple prop_Unit @-}
{-@ prop_Unit ::  x:Int -> { Lib.QC.Heap.prop_Unit x } @-}
prop_Unit ::  Int -> Proof
prop_Unit x = trivial
            -- (unit x ==? [x])
            -- === -- definition of ==?
            --   (let h = Node x empty empty in 
            --         (invariant h && sort (toList h) == sort [x])
            --     === (invariant h && sort (toList h) == sort [x])
            --     === (invariant h && sort (toList' [h]) == sort [x])
            --     === (invariant h && sort (x:toList' (Empty:Empty:[])) == sort [x])
            --     === (invariant h && sort (x:toList' (Empty:Empty:[])) == sort [x])
            --     === (invariant h && sort (x:toList' (Empty:[])) == sort [x])
            --     === (invariant h && sort (x:toList' []) == sort [x])
            --     === (invariant h && sort [x] == sort [x])
            --     === (invariant h)) 
            --     -- def. of invariant
            --     === (x <=? Empty && x <=? Empty && invariant (Empty::Heap Int) && invariant (Empty::Heap Int))
            -- --  === (True && True && True && True)
            -- ***QED



{-======================================================
                        prop_Size
=======================================================-}
------ Distributivity of toList' over (++)
{-@ ple distProp @-}
{-@ inline disToList @-}
disToList h1 h2 = toList' (h1++h2) == (toList' h1 ++ toList' h2)
{-@ distProp ::  Eq a =>  h1:[Heap a] -> h2:[Heap a] -> { disToList h1 h2 } @-}
distProp :: Eq a => [Heap a] -> [Heap a] -> Proof
distProp [] h2 = trivial
        -- ( toList' ([]++h2) == (toList' [] ++ toList' h2) )
        --                             ?  (toList' [] ++ toList' h2
        --                                === [] ++ toList' h2
        --                                === toList' h2
        --                                )
        --      === ( toList' h2 == toList' h2 )
        --           ***QED

distProp ((h@Empty):hs) h2 = trivial ? distProp hs h2 
        -- (toList' ((h:hs)++h2) == (toList' (h:hs) ++ toList' h2))
        --             ?(
        --                 toList' ((h:hs)++h2)
        --             === toList' (h:(hs++h2))
        --             === toList' (hs++h2)
        --             )
        --                                         ?(toList' (h:hs)
        --                                         === toList' hs
        --                                         )
        --             === (toList' (hs++h2) == toList' hs ++ toList' h2)
        --                ? distProp hs h2 
                      
        --          ***QED

distProp (h@(Node x hl hr):hs) h2 =  trivial
                                        
                                    ? lemma_distProp h (hs++h2)
                                    ? lemma_distProp h hs
                                   
                                    ? distProp hs h2
                                    ? assocP (toList' [h]) (toList' hs) (toList' h2)
            -- (toList' ((h:hs)++h2) == (toList' (h:hs) ++ toList' h2))
            -- ?(
            --     toList' ((h:hs)++h2)
            -- === toList' (h:(hs++h2))
            --     ? (  toList' (h:(hs++h2))
            --      ==! toList' [h] ++ toList' (hs++h2))
            -- === toList' [h] ++ toList' (hs++h2)
            --     ? distProp hs h2
            -- === toList' [h] ++ (toList' hs ++ toList' h2)
            --     ? assocP (toList' [h]) (toList' hs) (toList' h2)
            -- === (toList' [h] ++ toList' hs) ++ toList' h2
            --     ? (  toList' (h:hs)
            --      ==! toList' [h] ++ toList' hs)
                 
            -- === toList' (h:hs) ++ toList' h2
            -- )
            -- ***QED

{-@ ple lemma_distProp @-}
{-@ inline lemma_distProp_p @-}
lemma_distProp_p h hs = toList' (h:hs) == toList' [h] ++ toList' hs
{-@ lemma_distProp :: Eq a => h:Heap a -> hs:[Heap a] -> { lemma_distProp_p h hs } @-}
lemma_distProp :: Eq a => Heap a -> [Heap a] -> Proof
lemma_distProp h@Empty hs =  trivial
            -- toList' [h] ++ toList' hs
            --         ? (
            --             toList' [h]
            --         === toList' []
            --         === []
            --         )
            --     === [] ++ toList' hs
            --     === toList' hs
            --     === toList' (h:hs) 
            --     ***QED
lemma_distProp h@(Node x hl hr) hs = trivial
                                     ? lemma_distProp hl (hr:hs)
                                     ? lemma_distProp hr hs
                                     ? assocP (toList' [hl]) (toList' [hr]) (toList' hs)
                                     ? lemma_distProp hl [hr]
                --         toList' (h:hs)
                --         === x: toList' (hl:hr:hs)
                --             ? lemma_distProp hl (hr:hs)
                --         === x: (toList' [hl] ++ toList' (hr:hs))
                --                                 ? lemma_distProp hr hs
                --         === x: (toList' [hl] ++ (toList' [hr] ++ toList' hs))
                --                 ? assocP (toList' [hl]) (toList' [hr]) (toList' hs)
                --         === x: ((toList' [hl] ++ toList' [hr]) ++ toList' hs)
                --             ? lemma_distProp hl [hr]
                --         === x: ((toList' (hl:[hr])) ++ toList' hs)
                --         === x: toList' (hl:hr:[]) ++ toList' hs
                --         === (x: toList' (hl:hr:[])) ++ toList' hs
                --         === (toList' ([h])) ++ toList' hs
                -- ***QED
------ End Distributivity of toList' over (++)

{-@ ple prop_Size @-}
{-@ prop_Size ::  h:Heap Int -> { Lib.QC.Heap.prop_Size h } @-}
prop_Size ::  Heap Int -> Proof
prop_Size Empty =  trivial
                -- (size Empty == length (toList Empty))
                --   ===  ( 0 == length (toList' [Empty]))
                --   ===  ( 0 == length (toList' []))
                --   ===  ( 0 == length [])
                --   ***QED

prop_Size h@(Node v hl hr) =  
                            trivial
                            ? distProp [hl] [hr]
                            ? Heap_Proofs.prop_Size hl
                            ? Heap_Proofs.prop_Size hr
                            ? append_length (toList' [hl]) (toList' [hr])
            -- (size h == length (toList h)) -- apply size
            -- ===  (1 + size hl + size hr == length (toList' [h]))  -- apply toList'
            -- ===  (1 + size hl + size hr == length (v:toList' [hl,hr])) 
            --                 ? (    [hl]++[hr]
            --                 === hl:([]++[hr])
            --                 === hl:[hr] )
            -- === (1 + size hl + size hr == length (v:toList' ([hl]++[hr]))) -- distributivity of toList'
            --       ? distProp [hl] [hr]
            -- ===  (1 + size hl + size hr == length (v:(toList' [hl] ++ toList' [hr]))) -- def of length
            -- ===  (1 + size hl + size hr == 1 + length (toList' [hl] ++ toList' [hr])) -- mult. length
            -- ===  (1 + size hl + size hr == 1 + length (toList' [hl]) + length (toList' [hr])) -- toList' to toList
            -- === (1 + size hl + size hr == 1 + length (toList hl) + length (toList hr))
            --       ? Heap_Proofs.prop_Size hl
            --       ? Heap_Proofs.prop_Size hr
            -- === (size h == length (toList h)) 
            -- ***QED


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
                                )
                                ? (x: toList h
                                === x: toList' [h]
                                === x: toList' [empty,h]
                                === x: toList' [empty,empty,h]
                                === toList' [Node x empty empty, h]
                                    ? lemma_distProp (Node x empty empty) [h]
                                === toList' [Node x empty empty] ++ toList' [h]
                                === toList (Node x empty empty) ++ toList h
                                )
                            === (Node x empty empty) `merge` h ==? (toList (Node x empty empty) ++ toList h)
                                ? Heap_Proofs.prop_Merge (Node x empty empty) h
                                ? (Lib.QC.Heap.prop_Merge (Node x empty empty) h
                                === (Node x empty empty) `merge` h ==? (toList (Node x empty empty) ++ toList h))
                            === (Node x empty empty) `merge` h ==? toList' [Node x empty empty, h]
                ***QED

{-======================================================
                        prop_Merge
=======================================================-}
{-@ prop_Merge ::  h1:Heap Int -> h2:Heap Int -> { Lib.QC.Heap.prop_Merge h1 h2  } @-}
prop_Merge :: Heap Int -> Heap Int -> Proof

prop_Merge h1@Empty h2 =  Lib.QC.Heap.prop_Merge h1 h2 
                      === (h1 `merge` h2) ==? (toList h1 ++ toList h2)
                                              ?(toList Empty
                                            === toList' [Empty]
                                            === toList' []
                                            === [])
                      === (h2) ==? (toList h2)
                      === (invariant h2 && sort (toList h2) == sort (toList h2))
              ***QED

prop_Merge h1 h2@Empty =  Lib.QC.Heap.prop_Merge h1 h2 
                      === (h1 `merge` h2) ==? (toList h1 ++ toList h2)
                                              ?(toList Empty
                                            === toList' [Empty]
                                            === toList' []
                                            === [])
                                            ? rightIdP (toList h1)
                      === (h1) ==? (toList h1)
                      === (invariant h1 && sort (toList h1) == sort (toList h1))
                      ***QED

prop_Merge hl@(Node x h11 h12) hr@(Node y h21 h22) 
  | x<=y    = Lib.QC.Heap.prop_Merge hl hr
              ? req_order hl hr
              ? prop_Merge_subProof hl hr
            ***QED


  | otherwise = 
            Lib.QC.Heap.prop_Merge hl hr
          === (hl `merge` hr) ==? (toList hl ++ toList hr)
              -- def of merge
          === (hr `merge` hl) ==? (toList hl ++ toList hr)
          === (invariant (hr `merge` hl) && sort (toList (hr `merge` hl)) == sort (toList hl ++ toList hr))
          === sort (toList (hr `merge` hl)) == sort (toList hl ++ toList hr)
                                              --swap hl and hr
                                              ? th_sort_arg_rev (toList hl) (toList hr)
          === sort (toList (hr `merge` hl)) == sort (toList hr ++ toList hl)
          === (hr `merge` hl) ==? (toList hr ++ toList hl)
          === Lib.QC.Heap.prop_Merge hr hl
              ? req_order hr hl
              ? prop_Merge_subProof hr hl
          ***QED




{-======================================================
                        prop_ToSortedList
=======================================================-}
{-@ prop_ToSortedList :: h:Heap Int -> {Lib.QC.Heap.prop_ToSortedList h} @-}
prop_ToSortedList :: Heap Int -> Proof
prop_ToSortedList h@Empty = Lib.QC.Heap.prop_ToSortedList h
                  ===  (h ==? (toSortedList h) && 
                              (toSortedList h) == sort (toSortedList h))
                        ? (
                          h ==? []
                        === (invariant h && sort (toList h) == sort ([]))
                        === sort (toList h) == []
                                  ?(toList h
                                  === toList' [h]
                                  === toList' []
                                  === [])
                        === sort ([]::[Int]) == sort []
                        )
                     ***QED

prop_ToSortedList h@(Node x hl hr) = Lib.QC.Heap.prop_ToSortedList h
                  ===  (h ==? (toSortedList h) && 
                              (toSortedList h) == sort (toSortedList h))
                        ? (
                          h ==? (toSortedList h)
                        === (invariant h && sort (toList h) == sort (toSortedList h))
                        === sort (toList h) == sort (toSortedList h)
                                ?(toList h
                              === toList' [h]
                              === x : toList' [hl,hr]
                                      ? lemma_distProp hl [hr]
                              === x : (toList' [hl] ++ toList' [hr])
                              === x : (toList hl ++ toList hr))
                        === sort (x : (toList hl ++ toList hr)) == sort (x : toList (hl `merge` hr))
                                                                    ? th_sort_arg_cons x (toList (hl `merge` hr))
                                    ? th_sort_arg_cons x (toList hl ++ toList hr)
                        === sort (x : sort (toList hl ++ toList hr)) == sort (x : sort (toList (hl `merge` hr)))
                              ? Heap_Proofs.prop_Merge hl hr
                              ? (
                                Lib.QC.Heap.prop_Merge hl hr
                              ===  hl `merge` hr ==? (toList hl ++ toList hr)
                              === (invariant (hl `merge` hr) && sort (toList (hl `merge` hr)) == sort (toList hl ++ toList hr))
                              === sort (toList (hl `merge` hr)) == sort (toList hl ++ toList hr)
                              )
                        )
                  === (toSortedList h) == sort (toSortedList h)
                  === (x : toList (hl `merge` hr)) == sort (x : toList (hl `merge` hr))
                  ***Admit

{-======================================================
                        prop_RemoveMin
=======================================================-}
{-@ prop_RemoveMin :: h:Heap Int -> { Lib.QC.Heap.prop_RemoveMin h } @-}
prop_RemoveMin :: Heap Int ->  Proof
prop_RemoveMin h@Empty =  Lib.QC.Heap.prop_RemoveMin h
                        ? (removeMin h === Nothing)
                      === h ==? []
                      === (invariant h && sort (toList h) == sort [])
                          ? (invariant h === True)
                          ? (sort (toList h)
                          === sort (toList' [h])
                          === sort (toList' [])
                          === sort []
                          )
                      ***QED

prop_RemoveMin h@(Node x h1 h2) =   Lib.QC.Heap.prop_RemoveMin h
                                    ? (removeMin h === Just (x, h1 `merge` h2))
                                === ( let  Just (x,h') = removeMin h
                                    in (x == minimum (toList h) && h' ==? (toList h \\ [x]))
                                      ?(toList h
                                      === toList' [h]
                                      === x:toList' [h1,h2]
                                      )
                                    )
                                ***Admit




---------------------------------
{-@ inline req_only_node @-}
req_only_node ::  Heap Int -> Bool
req_only_node h = case h of
                    Empty -> False
                    Node _ _ _ -> True
------------------
{-@ reflect req_order @-}
req_order ::  Heap Int -> Heap Int -> Bool
req_order  (Node x _ _) (Node y _ _) = x<=y
req_order _ _  = False
------------------
-- subproof of case x<=y 
{-@ prop_Merge_subProof :: hl:{Heap Int | req_only_node hl } -> 
                           hr:{Heap Int | req_only_node hr && req_order hl hr } -> { Lib.QC.Heap.prop_Merge hl hr } @-}
prop_Merge_subProof ::  Heap Int -> Heap Int -> Proof
prop_Merge_subProof (Node x h11 h12) (Node y h21 h22) = 
                      let hl=Node x h11 h12
                          hr=Node y h21 h22
                      in 
                        Lib.QC.Heap.prop_Merge hl hr
                        === (hl `merge` hr) ==? (toList hl ++ toList hr)
                        === (invariant (hl `merge` hr)  && sort (toList (hl `merge` hr)) == sort (toList hl ++ toList hr))
                        -- ===  sort (toList (hl `merge` hr)) == sort (toList hl ++ toList hr)
                        --           ?(hl `merge` hr --apply merge
                        --           ?(req_order hl hr) -- needed to highlight x<=y
                        --           === Node x (h12 `merge` hr) h11)
                        --           ?(
                        --             (toList (Node x (h12 `merge` hr) h11)) --apply toList
                        --           === (toList' [Node x (h12 `merge` hr) h11])
                        --           === (x : toList' [(h12 `merge` hr), h11])
                        --                     ? lemma_distProp (h12 `merge` hr) [h11]
                        --           === (x : (toList' [(h12 `merge` hr)] ++ toList' [h11]))
                        --           === (x : (toList (h12 `merge` hr) ++ toList' [h11]))
                        --           )
                        -- ===  sort (x : (toList (h12 `merge` hr) ++ toList' [h11])) == sort (toList hl ++ toList hr)
                        --                   ?(
                        --                     sort (x : (toList (h12 `merge` hr) ++ toList' [h11]))
                        --                           ? th_sort_arg_cons x (toList (h12 `merge` hr) ++ toList' [h11])
                        --                   === sort (x : sort (toList (h12 `merge` hr) ++ toList' [h11]))
                        --                   )
                        --                   ?(
                        --                     sort (toList (h12 `merge` hr) ++ toList' [h11])
                        --                       ? th_sort_arg_app (toList (h12 `merge` hr)) (toList' [h11])
                        --                   === sort ( sort (toList (h12 `merge` hr)) ++ toList' [h11])
                        --                   ) 
                        --                   ?(sort (toList (h12 `merge` hr))
                        --                         ? Heap_Proofs.prop_Merge h12 hr
                        --                         ? (Lib.QC.Heap.prop_Merge h12 hr
                        --                         === (h12 `merge` hr ==? (toList h12  ++ toList hr))
                        --                         === (invariant (h12 `merge` hr) && sort(toList(h12 `merge` hr)) == sort (toList h12  ++ toList hr))
                        --                         === sort(toList(h12 `merge` hr)) == sort (toList h12  ++ toList hr)
                        --                         )
                        --                   === sort (toList h12  ++ toList hr)
                        --                   )
                        -- === sort (x : sort ( sort (toList h12  ++ toList hr) ++ toList' [h11])) == sort (toList hl ++ toList hr)
                        --     -- delete the this ^^ sort
                        --     ?(sort ( sort (toList h12  ++ toList hr) ++ toList' [h11]) 
                        --         ? th_sort_arg_app (toList h12  ++ toList hr) (toList' [h11]) 
                        --     === sort ((toList h12  ++ toList hr) ++ toList' [h11])
                        --     -- reorder the these ^^^^^^ appends
                        --         ? th_sort_arg_rev (toList h12  ++ toList hr) (toList' [h11])
                        --     === sort (toList' [h11] ++ (toList h12  ++ toList hr))
                        --         ? assocP (toList' [h11]) (toList h12) (toList hr)
                        --     === sort (toList' [h11] ++ toList h12  ++ toList hr)
                        --     )
                        -- === sort (x : sort (toList' [h11] ++ toList h12  ++ toList hr)) == sort (toList hl ++ toList hr)
                        --      -- delete ^^^ this sort
                        --      ?( sort (x : sort (toList' [h11] ++ toList h12  ++ toList hr))
                        --             ? th_sort_arg_cons x (toList' [h11] ++ toList h12  ++ toList hr)
                        --       === sort (x : (toList' [h11] ++ toList h12  ++ toList hr))
                        --       )
                        --       -- join these appends ^^^^
                        --       ?(toList' [h11] ++ toList h12  ++ toList hr
                        --       === (toList' [h11] ++ toList' [h12])  ++ toList' [hr]
                        --             ? distProp [h11] [h12]
                        --       === (toList' ([h11] ++ [h12]))  ++ toList' [hr]
                        --                   ? ([h11]++[h12]
                        --                   ===h11:([]++[h12])
                        --                   ===[h11,h12])
                        --       === (toList' [h11,h12]  ++ toList' [hr])
                        --            ? distProp [h11,h12] [hr]
                        --       === toList' ([h11,h12]++ [hr])
                        --                   ?([h11,h12]++ [hr]
                        --                   === h11:([h12]++[hr])
                        --                   === h11:h12:([]++[hr])
                        --                   === [h11,h12,hr])
                        --       === toList' ([h11,h12,hr])
                        --       )
                        ==! sort (x : sort (toList' [h11,h12,hr])) == sort (toList hl ++ toList hr)
                            -- ?(sort (x : sort (toList' [h11,h12,hr]))
                            -- --  delete ^this sort
                            --     ? th_sort_arg_cons x (toList' [h11,h12,hr])
                            -- === sort (x :(toList' [h11,h12,hr]))
                            -- === sort (toList' [(Node x h11 h12),hr])
                            -- === sort (toList' [hl,hr])
                            --           ? lemma_distProp hl [hr]
                            -- === sort (toList' [hl] ++ toList'[hr])
                            -- === sort (toList hl ++ toList hr)
                            --   )
                        ***Admit

