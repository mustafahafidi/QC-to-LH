{-# LANGUAGE  QuasiQuotes #-}
{-# OPTIONS_GHC -dth-dec-file #-}

module TH.Heap_Test where


import TH.ProofGenerator (lhp)

import Lib.QC.Heap 
import Prelude  hiding (length, 
                        (++), 
                        reverse, 
                        iterate, 
                        null, 
                        splitAt,
                        any
                        )
import Lib.LH.Prelude 
import Language.Haskell.Liquid.ProofCombinators
import Heap_Proofs (distProp, req_order, prop_Merge_subProof)

{-@ LIQUID "--reflection"    @-}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--ple-local"    @-}
-- {-@ LIQUID "--diff"    @-}


[lhp|genProp|reflect|ple

prop_Empty :: Bool
prop_Empty = empty ==? ([] :: [Int])

|]


-- needs pattern matching
[lhp|genProp|reflect|ple|caseExpand

prop_IsEmpty :: Heap Int -> Bool
prop_IsEmpty h = isEmpty h == null (toList h)

|]



[lhp|genProp|reflect|ple

prop_Unit :: Int -> Bool
prop_Unit x = unit x ==? [x]

|]

-- Deep properties

[lhp|genProp|reflect|ple
prop_Size ::  Heap Int -> Bool
prop_Size h@(Node v hl hr)  = ()
                ? distProp [hl] [hr]
                ? prop_Size_proof hl
                ? prop_Size_proof hr
                ? append_length (toList' [hl]) (toList' [hr]) 
                
prop_Size h  = size h == length (toList h) 
|]


[lhp|genProp|reflect|ple
prop_Insert :: Int -> Heap Int -> Bool
prop_Insert x h = insert x h ==? (x : toList h)
                ? prop_Merge_proof (Node x empty empty) h

|]

[lhp|genProp|reflect|ple
prop_Merge :: Heap Int -> Heap Int -> Bool
prop_Merge hl@(Node x _ _) hr@(Node y _ _) 
  | x<=y    = ()
            ? prop_Merge_subProof hl hr
  | otherwise = ()
                ? prop_Merge_subProof hr hl
                ? th_sort_arg_rev (toList hl) (toList hr)

prop_Merge h1 h2 = (h1 `merge` h2) ==? (toList h1 ++ toList h2)
                    ? invariant h1
                    ? invariant h2
                    ? rightIdP (toList h1)
|]