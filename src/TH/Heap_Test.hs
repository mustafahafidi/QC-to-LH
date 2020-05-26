{-# LANGUAGE  QuasiQuotes #-}

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

{-@ LIQUID "--reflection"    @-}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--ple-local"    @-}


[lhp|genProp|reflect|ple

prop_Empty :: Bool
prop_Empty = empty ==? ([] :: [Int])

|]


-- needs pattern matching
[lhp|genProp|reflect|ple|ignore

prop_IsEmpty :: Heap Int -> Bool
prop_IsEmpty h = isEmpty h == null (toList h)

|]



[lhp|genProp|reflect|ple

prop_Unit :: Int -> Bool
prop_Unit x = unit x ==? [x]

|]



[lhp|genProp|reflect|ple

prop_Size :: Heap Int -> Bool
prop_Size h@Empty  = size h == length (toList h)
prop_Size h@(Node v hl hr)  = size h == length (toList h)
                ? toList_distProp_proof [hl] [hr]
               ? prop_Size_proof hl
                ? prop_Size_proof hr
                ? length_append_dist_proof (toList' [hl]) (toList' [hr])

|]


[lhp|genProp|reflect|ple|ignore

toList_distProp :: Eq a => [Heap a] -> [Heap a] -> Bool
toList_distProp h1 h2 = toList' (h1++h2) == (toList' h1 ++ toList' h2)

|]

[lhp|genProp|reflect|admit

length_append_dist ::  [a] -> [a] -> Bool
length_append_dist ls rs = length (ls ++ rs) == length ls + length rs

|]