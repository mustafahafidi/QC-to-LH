{-# OPTIONS_GHC -dth-dec-file #-}
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

{-@ LIQUID "--no-adt" @-}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--reflection"    @-}
{-@ LIQUID "--ple-local"    @-}
{-@ LIQUID "--diff"    @-}



[lhp|genProp|reflect|ple

prop_empty :: Bool
prop_empty = length (toList empty) == 0
|]



-- with no-adt ple is not sufficient anymore, needs pattern matching
[lhp|genProp|reflect|ple|caseExpand
prop_isEmpty :: [Int] -> Bool
prop_isEmpty l = null l == isEmpty (fromList l)
|]




[lhp|genProp|reflect|ple

prop_size :: [Int] -> Bool
prop_size l = (length l) == (size . fromList $ l)
|]


-- with no-adt ple is not sufficient anymore, needs pattern matching
[lhp|genProp|reflect|ple|caseExpand

prop_focus :: CList Int -> Int -> Bool
prop_focus c v = (Just v) == (focus $ insertR v c)
|]


--  Additional properties

[lhp|genProp|reflect|ple

prop_singleton :: Int -> Bool
prop_singleton i = toList (singleton i) == [i]
|]



[lhp|genProp|reflect|ple|caseExpand

prop_update :: Int -> CList Int -> Bool
prop_update v cl = case cl of
                        Empty -> size (update v cl) == 1
                        _     -> size (update v cl) == size cl
|]


 

[lhp|genProp|reflect|ple|caseExpand

prop_focus_update :: Int -> CList Int -> Bool
prop_focus_update v cl = focus(update v cl) == Just v

|]



[lhp|genProp|reflect|ple|caseExpand

prop_reverse_direction ::  CList Int -> Bool
prop_reverse_direction cl = reverseDirection (reverseDirection cl) == cl && size (reverseDirection cl) == size cl

|]



[lhp|genProp|reflect|ple|caseExpand

prop_insertR :: Int -> CList Int -> Bool
prop_insertR i cl = let r = (insertR i cl) in
                        size r == size cl+1

|]


[lhp|genProp|reflect|ple
prop_removeR ::  CList Int -> Bool
prop_removeR cl@(CList [] _ []) = trivial
prop_removeR cl@(CList l@(_:_) p433 []) = size (removeR cl)
                                === (let (f:rs)=reverse l in
                                     size(CList [] f rs)) 
                                ===  (size cl)-1
                                
prop_removeR cl = case cl of
                    Empty -> size (removeR cl) == 0
                    _     -> size (removeR cl) == (size cl)-1
|]


[lhp|genProp|reflect|ple|caseExpand

prop_insertR_removeR :: Int -> CList Int -> Bool
prop_insertR_removeR v cl = removeR (insertR v cl) == cl

|]

[lhp|genProp|reflect|ple

prop_fromList_focus :: Bool
prop_fromList_focus = focus (fromList ([1]::[Int])) == Just 1

|]

------- Deep properties
{-@ reflect eqf @-}
eqf ::  CList Int -> CList Int -> Bool
eqf a b = toList a == toList b

{-@ reflect =*= @-}
{-@ infix 4 =*= @-}
(=*=) :: CList Int -> CList Int -> Bool
x =*= y = (any (eqf x) (toList (allRotations y)))

[lhp|genProp|reflect|ple|caseExpand
lemma_refl :: CList Int -> Bool
lemma_refl cl = cl =*= cl
|]

-- {-@ LIQUID "--nototality" @-} --necessary because of
[lhp|genProp|reflect|ple
prop_list :: CList Int -> Bool
prop_list c@Empty = (c =*= (fromList . toList $ c))
                    ? (lemma_refl_proof c)
prop_list c@(CList l f r) = (c =*= (fromList . toList $ c))
        ? (let
                a@(i:is) = f : (r ++ (reverse l))
                len = length a
                (sr,sl) = splitAt (len `div` 2) is
                b = CList (reverse sl) i sr
            in  c =*= b
                ? involutionP sl
                ? splitAt_theorem (len `div` 2) is
            )

prop_list c = (c =*= (fromList . toList $ c))
|]

[lhp|genProp|reflect|ple
prop_rot :: CList Int -> Bool
prop_rot c@(CList [] f rs@(_:_))  =   c =*= (rotR  (rotL c))
                            ? ((rotR (rotL c))
                            === (let (l:ls) = reverse rs
                                        in rotR (CList ls l [f])
                                )
                            )
                            === c =*= (CList (reverse rs) f [])
                                ? involutionP rs
                                ? rightIdP rs
prop_rot c = c =*= (rotR $ rotL c)
|]


[lhp|genProp|reflect|ple|caseExpand
prop_packL ::  CList Int -> Bool
prop_packL c@(CList l f r) = c =*= (packL c)
        ? (distributivityP l (reverse r))
        ? involutionP r

prop_packL c = c =*= (packL c)
|]


-- prop_packL :: CList Int -> Bool
-- prop_packL c = c =*= (packL c)

-- [lhp|genProp|reflect

-- prop_packR :: CList Int -> Bool
-- prop_packR c@Empty = c =*= (packR c)
--                 ? lemma_refl c
-- prop_packR c = c =*= (packR c)
--                 ?(()***Admit)

-- |]

