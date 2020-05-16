module Lib.QC.ExtraTheorems where
import Lib.LH.Prelude ((++), reverse, sort, insertSort, assocP)
import Prelude hiding ((++), reverse)
import Language.Haskell.Liquid.ProofCombinators
import Lib.QC.Heap
-- import Heap_Proofs
{-@ LIQUID "--reflection"    @-}
{-@ LIQUID "--shortnames" @-}

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
