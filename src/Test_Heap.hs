
module Test_Heap where

import Lib.QC.Heap --(merge, Heap(..), (==?), toList)
import Lib.LH.Prelude
import Heap_Proofs
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (length, 
                        (++), 
                        reverse, 
                        iterate, 
                        null, 
                        splitAt,
                        any,
                        id,
                        minimum,
                        Maybe (..)
                        )

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--short-names" @-}
-- {-@ LIQUID "--diff"        @-}
-- {-@ LIQUID "--notermination" @-} 

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







{-@ inline req_only_node @-}
req_only_node ::  Heap Int -> Bool
req_only_node h = case h of
                    Empty -> False
                    Node _ _ _ -> True

{-@ reflect req_order @-}
-- {-@ req_order ::  Heap Int -> Heap Int -> { req_order} @-}
req_order ::  Heap Int -> Heap Int -> Bool
req_order  (Node x _ _) (Node y _ _) = x<=y
req_order _ _  = False

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
                        --                         ? Test_Heap.prop_Merge h12 hr
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
