{-# LANGUAGE  QuasiQuotes #-}

module TH.CList_Test where

import TH.ProofGenerator (lhp)

import Lib.CL.CircularList 
-- import CList_Proofs ((=*=))
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
-- {-@ LIQUID "--diff"    @-}
{-@ LIQUID "--ple-local"    @-}



[lhp|genProp|reflect|ple

prop_empty :: Bool
prop_empty = length (toList empty) == 0
|]




[lhp|genProp|reflect|ple

prop_isEmpty :: [Int] -> Bool
prop_isEmpty l = null l == isEmpty (fromList l)
|]




[lhp|genProp|reflect|ple

prop_size :: [Int] -> Bool
prop_size l = (length l) == (size . fromList $ l)
|]



[lhp|genProp|reflect|ple

prop_focus :: CList Int -> Int -> Bool
prop_focus c v = (Just v) == (focus $ insertR v c)
|]


--  Additional properties

[lhp|genProp|reflect|ple

prop_singleton :: Int -> Bool
prop_singleton i = toList (singleton i) == [i]
|]



[lhp|genProp|reflect|ple

prop_update :: Int -> CList Int -> Bool
prop_update v cl@Empty = size (update v cl) == 1
prop_update v cl = size (update v cl) == size cl
|]



[lhp|genProp|reflect|ple

prop_focus_update :: Int -> CList Int -> Bool
prop_focus_update v cl = focus(update v cl) == Just v

|]



[lhp|genProp|reflect|ple

prop_reverse_direction ::  CList Int -> Bool
prop_reverse_direction cl = reverseDirection (reverseDirection cl) == cl && size (reverseDirection cl) == size cl

|]



[lhp|genProp|reflect|ple

prop_insertR :: Int -> CList Int -> Bool
prop_insertR i cl = let r = (insertR i cl) in
                        size r == size cl+1

|]



-- needs refinement type
[lhp|genProp|reflect|ple|ignore

prop_removeR :: CList Int -> Bool
prop_removeR cl@Empty = size (removeR cl) == 0
prop_removeR cl = size (removeR cl) == (size cl)-1

|]



--needs pattern matching
[lhp|genProp|reflect|ple|ignore

prop_insertR_removeR :: Int -> CList Int -> Bool
prop_insertR_removeR v cl = removeR (insertR v cl) == cl

|]


[lhp|genProp|reflect|ple

prop_fromList_focus :: Bool
prop_fromList_focus = focus (fromList ([1]::[Int])) == Just 1

|]

-- Deep properties 

{-@ reflect =*= @-}
{-@ infix 4 =*= @-}
(=*=) :: Eq a  => CList a -> CList a -> Bool
a =*= b = (any ((toList a ==) . toList) . toList $ allRotations b)


-- prop_list :: CList Int -> Bool
-- prop_list c = c =*= (fromList . toList $ c)

-- -- {-@ inline prop_rot @-}
-- prop_rot :: CList Int -> Bool
-- prop_rot c = c =*= (rotR $ rotL c)

-- prop_packL :: CList Int -> Bool
-- prop_packL c = c =*= (packL c)

[lhp|genProp|reflect|ple

prop_packR :: CList Int -> Bool
prop_packR c@Empty = c =*= (packR c)
                ? lemma_refl c
prop_packR c = c =*= (packR c)
                ?(()***Admit)

|]


-- ple crashes here (SMTLIB) thus can't use it in prop_packR
[lhp|genProp|reflect|ignore

lemma_refl :: Eq a => CList a -> Bool
lemma_refl cl = cl =*= cl

|]