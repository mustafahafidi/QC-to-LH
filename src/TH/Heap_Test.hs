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
prop_Size h  = size h == length (toList h)

|]