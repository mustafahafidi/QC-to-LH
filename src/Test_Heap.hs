
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
{-@ LIQUID "--ple-local" @-}


{-======================================================
                        prop_Insert
=======================================================-}
-- {-@ ple prop_Insert @-}
{-@ prop_Insert ::  x:Int -> hp:Heap Int -> { Lib.QC.Heap.prop_Insert x hp } @-}
prop_Insert ::  Int -> Heap Int -> Proof
prop_Insert x Empty =  trivial 
                        ? invariant (insert x Empty)
                --     ( insert x Empty ==? (x : toList Empty) )
                --                             ? (
                --                                 (x : toList' [Empty])
                --                             === x : toList' []
                --                             === [x]
                --                             )
                --     ===  ( insert x Empty ==? [x])
                --     === (let h = insert x Empty
                --         in (invariant h && sort (toList h) == sort [x])
                --         )
                --     === (sort (toList (insert x Empty)) == sort [x])
                --              ?(
                --                 (toList (insert x Empty))
                --             === (toList ( unit x `merge` Empty))
                --             === (toList ( (Node x empty empty) `merge` Empty))
                --             === (toList (Node x empty empty))
                --             === (toList' [Node x Empty Empty])
                --             === (x : toList' (Empty:Empty:[]))
                --             === (x : toList' (Empty:[]))
                --             === (x : toList' ([]))
                --             === ([x]) 
                --              )
                -- ***QED 

prop_Insert x h@(Node y hl hr)
            | x <= y    = trivial 
                            ? invariant (Node x h Empty) 
                             ? distProp [hl,hr]  [Empty]
                             ? rightIdP (toList' [hl,hr])
                            ? (unit x `merge` h
                            === Node x empty empty `merge` h
                            )
                        -- let h= (Node y hl hr)
                        -- in (insert x h ==? (x : toList h))
                        --     ? (insert x h ==! Node x (Node y hl hr) Empty)
                        --                         ? (x:toList h  ==! (x : y : toList' [hl,hr]))
                        -- ===  ((Node x h Empty) ==? (x : y : toList' [hl,hr]))
                        -- === (invariant (Node x h Empty) 
                        --         && sort (toList (Node x h Empty)) == sort (x : y : toList' [hl,hr]))
                        -- === sort (toList (Node x h Empty)) == sort (x : y : toList' [hl,hr])
                        --         ?(
                        --           toList (Node x h Empty)
                        --         === toList' ([Node x h Empty])
                        --         === x:toList' ([h,Empty])
                        --         === x:y:toList' ([hl,hr,Empty])
                        --                         ?( [hl,hr,Empty]
                        --                         === hl:hr:[Empty]
                        --                         === hl:hr:([]++[Empty])
                        --                         === hl:([hr]++[Empty])
                        --                         === [hl,hr]++[Empty]
                        --                         )
                        --             ? distProp [hl,hr]  [Empty]
                        --         === x:y:( toList' [hl,hr] ++ toList' [Empty] )
                        --                                     ?(
                        --                                         toList' [Empty]
                        --                                     === toList' []
                        --                                     === []
                        --                                     )
                        --                                     ?rightIdP (toList' [hl,hr])
                        --         === x:y:( toList' [hl,hr] )
                        --         )
                        -- ***QED
 
            | otherwise = 
                        let h = (Node y hl hr)
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
