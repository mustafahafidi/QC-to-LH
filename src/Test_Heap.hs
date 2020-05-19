
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
{-@ LIQUID "--notermination" @-} 

-- {-@ lemma_proof ::  Proof @-}
-- lemma_proof ::  Proof
-- lemma_proof hl hr = True ***QED

{-@ prop_Merge ::  h1:Heap Int -> h2:Heap Int -> { Lib.QC.Heap.prop_Merge h1 h2  } @-}
prop_Merge :: Heap Int -> Heap Int -> Proof

prop_Merge h1@Empty h2 =  (h1 `merge` h2) ==? (toList h1 ++ toList h2)     
              ***Admit

prop_Merge h1 h2@Empty =  (h1 `merge` h2) ==? (toList h1 ++ toList h2)     
              ***Admit

prop_Merge hl@(Node x h11 h12) hr@(Node y h21 h22) 
  | x<=y    = let hl=Node x h11 h12
                  hr=Node y h21 h22 
        in 
          Lib.QC.Heap.prop_Merge hl hr
          === (hl `merge` hr) ==? (toList hl ++ toList hr)
          === (invariant (hl `merge` hr)  && sort (toList (hl `merge` hr)) == sort (toList hl ++ toList hr))
          -- ===  sort (toList (hl `merge` hr)) == sort (toList hl ++ toList hr)
          --           ?(hl `merge` hr --apply merge
          --           === Node x (h12 `merge` hr) h11)
          --           ?(
          --             (toList (Node x (h12 `merge` hr) h11)) --apply toList
          --           === (toList' [Node x (h12 `merge` hr) h11])
          --           === (x : toList' [(h12 `merge` hr), h11])
          --                     ? lemma_distProp (h12 `merge` hr) [h11]
          --           ==! (x : (toList' [(h12 `merge` hr)] ++ toList' [h11]))
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
          --     === sort ((toList h12  ++ toList hr) ++ toList' [h11]))
          --     -- reorder the these ^^^^^^ appends
          --     ?((toList h12  ++ toList hr) ++ toList' [h11]
          --       ==! (toList' [h11] ++ toList h12  ++ toList hr)
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


  | otherwise = 
    let hl=Node x h11 h12
        hr=Node y h21 h22 
        in  
            Lib.QC.Heap.prop_Merge hl hr
          === (hl `merge` hr) ==? (toList hl ++ toList hr)
              -- ?((hl `merge` hr)
              -- ==! (hr `merge` hl))
          === (hr `merge` hl) ==? (toList hl ++ toList hr)
          === (invariant (hr `merge` hl) && sort (toList (hr `merge` hl)) == sort (toList hl ++ toList hr))
          === sort (toList (hr `merge` hl)) == sort (toList hl ++ toList hr)
                                              --swap hl and hr
                                              ? th_sort_arg_rev (toList hl) (toList hr)
          === sort (toList (hr `merge` hl)) == sort (toList hr ++ toList hl)
          === (hr `merge` hl) ==? (toList hr ++ toList hl)
          === Lib.QC.Heap.prop_Merge hr hl
              ? Test_Heap.prop_Merge hr hl
          {- 
          Lib.QC.Heap.prop_Merge hl hr
          === (hl `merge` hr) ==? (toList hl ++ toList hr)
          === (invariant (hl `merge` hr)  && sort (toList (hl `merge` hr)) == sort (toList hl ++ toList hr))
          ===  sort (toList (hl `merge` hr)) == sort (toList hl ++ toList hr)
                    ?(hl `merge` hr --apply merge
                    === Node y (h22 `merge` Node x h11  h12) h21)
                    ?(
                      (toList (Node y (h22 `merge` hl) h21))--apply toList
                    === (toList' [Node y (h22 `merge` hl) h21])
                    === (y : toList' [(h22 `merge` hl), h21])
                              ? lemma_distProp (h22 `merge` hl) [h21]
                    === (y : (toList' [(h22 `merge` hl)] ++ toList' [h21]))
                    === (y : (toList (h22 `merge` hl) ++ toList' [h21]))
                    )
          ===  sort (y : (toList (h22 `merge` hl) ++ toList' [h21])) == sort (toList hl ++ toList hr)
                            ?(-- insert sort inside
                              sort (y : (toList (h22 `merge` hl) ++ toList' [h21]))
                                    ? th_sort_arg_cons y (toList (h22 `merge` hl) ++ toList' [h21])
                            === sort (y : sort (toList (h22 `merge` hl) ++ toList' [h21]))
                            )
                            ?(-- insert another ^^ sort here
                              sort (toList (h22 `merge` hl) ++ toList' [h21])
                                ? th_sort_arg_app (toList (h22 `merge` hl)) (toList' [h21])
                            === sort ( sort (toList (h22 `merge` hl)) ++ toList' [h21])
                            ) 
                            ?(sort (toList (h22 `merge` hl))
                                  ? Test_Heap.prop_Merge h22 hl
                                  ? (Lib.QC.Heap.prop_Merge h22 hl
                                  === (h22 `merge` hl ==? (toList h22  ++ toList hl))
                                  === (invariant (h22 `merge` hl) && sort(toList(h22 `merge` hl)) == sort (toList h22  ++ toList hl))
                                  === sort(toList(h22 `merge` hl)) == sort (toList h22  ++ toList hl)
                                  )
                            === sort (toList h22  ++ toList hl)
                            )-} 
          -- === sort (y : sort ( sort (toList h12  ++ toList hr) ++ toList' [h11])) == sort (toList hl ++ toList hr)
          --     -- delete the this ^^ sort
          --     ?(sort ( sort (toList h12  ++ toList hr) ++ toList' [h11]) 
          --         ? th_sort_arg_app (toList h12  ++ toList hr) (toList' [h11]) 
          --     === sort ((toList h12  ++ toList hr) ++ toList' [h11]))
          --     -- reorder the these ^^^^^^ appends
          --     ?((toList h12  ++ toList hr) ++ toList' [h11]
          --       ==! (toList' [h11] ++ toList h12  ++ toList hr)
          --     )
          -- === sort (y : sort (toList' [h11] ++ toList h12  ++ toList hr)) == sort (toList hl ++ toList hr)
          --      -- delete ^^^ this sort
          --      ?( sort (y : sort (toList' [h11] ++ toList h12  ++ toList hr))
          --             ? th_sort_arg_cons y (toList' [h11] ++ toList h12  ++ toList hr)
          --       === sort (y : (toList' [h11] ++ toList h12  ++ toList hr))
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
          ***QED