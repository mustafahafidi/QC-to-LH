{-# LANGUAGE ScopedTypeVariables, TemplateHaskell #-}
module Lib.QC.Heap where

--------------------------------------------------------------------------
-- imports

import Test.QuickCheck hiding((===))

import Data.List
  ( --sort
 (\\)
  )

import Control.Monad
  ( liftM
  , liftM2
  )


import Prelude hiding (length, (++), reverse, iterate, null, splitAt)
import Lib.LH.Prelude
import Language.Haskell.Liquid.ProofCombinators
--------------------------------------------------------------------------
-- skew heaps

{-@ LIQUID "--reflection"    @-}
{-@ LIQUID "--no-totality"    @-}
{-@ LIQUID "--no-termination"    @-}
{-@ LIQUID "--short-names"    @-}
-- {-@ LIQUID "--prune-unsorted"    @-}


data Heap a
  = Node a (Heap a) (Heap a)
  | Empty
 deriving ( Eq, Ord, Show )

{-@ 
data Heap a = Node { 
         k :: a
        , left  :: Heap {v:a | k <= v}
        , right :: Heap {v:a | k <= v} }
        | Empty 
@-}

-- {-@ 
-- data Heap a = Node { 
--          k :: a,
--          left  :: {hl:Heap a|Lib.QC.Heap.invariant hl},
--          right :: {hr:Heap a|Lib.QC.Heap.invariant hr && Lib.QC.Heap.invariant (Node k left hr)} 
--         }
--         | Empty
-- @-}


{-@ reflect empty @-}
empty :: Heap a
empty = Empty

{-@ reflect isEmpty @-}
isEmpty :: Heap a -> Bool
isEmpty Empty = True
isEmpty _     = False

-- {-@ ignore unit @-}
{-@ inline unit @-}
unit :: a -> Heap a
unit x = Node x empty empty

{-@ reflect size @-}
size :: Heap a -> Int
size Empty          = 0
size (Node _ h1 h2) = 1 + size h1 + size h2

{-@ reflect insert @-}
insert :: Ord a => a -> Heap a -> Heap a
insert x h = unit x `merge` h

removeMin :: Ord a => Heap a -> Maybe (a, Heap a)
removeMin Empty          = Nothing
removeMin (Node x h1 h2) = Just (x, h1 `merge` h2)


{-@ reflect merge @-}
merge :: Ord a => Heap a -> Heap a -> Heap a
h1    `merge` Empty = h1
Empty `merge` h2    = h2
h1@(Node x h11  h12) `merge` h2@(Node y h21 h22)
  | x <= y    = Node x (h12 `merge` Node y h21 h22) h11
  | otherwise = Node y (h22 `merge` Node x h11  h12) h21

fromList :: Ord a => [a] -> Heap a
fromList xs = merging [ unit x | x <- xs ]
 where
  merging []  = empty
  merging [h] = h
  merging hs  = merging (sweep hs)

  sweep []         = []
  sweep [h]        = [h]
  sweep (h1:h2:hs) = (h1 `merge` h2) : sweep hs

{-@ reflect toList @-}
toList :: Heap a -> [a]
toList h = toList' [h]

{-@ reflect toList' @-}
toList' :: [Heap a] -> [a]
toList' []                  = []
toList' (Empty        : hs) = toList' hs
toList' (Node x h1 h2 : hs) = x : toList' (h1:h2:hs)

toSortedList :: Ord a => Heap a -> [a]
toSortedList Empty          = []
toSortedList (Node x h1 h2) = x : toList (h1 `merge` h2)

--------------------------------------------------------------------------
-- specification

{-@ reflect invariant @-}
{-@  invariant ::  Ord a => Heap a -> { v :Bool | v <=> true  } @-}
invariant :: Ord a => Heap a -> Bool
invariant Empty          = True
invariant (Node x h1 h2) = x <=? h1 && x <=? h2 && invariant h1 && invariant h2


{-@ infix <=? @-}
{-@ reflect <=? @-}
{-@ (<=?) :: Ord a => x:a -> Heap {v:a | x <= v } -> {v:Bool | v <=> true } @-}
(<=?) :: Ord a => a -> Heap a -> Bool
x <=? Empty      = True
x <=? Node y _ _ = x <= y

{-@ infix ==? @-}
{-@ reflect ==? @-}
(==?) :: Ord a => Heap a -> [a] -> Bool
h ==? xs = invariant h && sort (toList h) == sort xs
-- skew heap
--------------------------------------------------------------------------
-- properties
{-@ inline prop_Empty @-}
prop_Empty =
  empty ==? ([] :: [Int])

{-@ inline prop_IsEmpty @-}
prop_IsEmpty (h :: Heap Int) =
  isEmpty h == null (toList h)

{-@ inline prop_Unit @-}
prop_Unit (x :: Int) =
  unit x ==? [x]

{-@ inline prop_Size @-}
prop_Size (h :: Heap Int) =
  size h == length (toList h)

{-@ inline prop_Insert @-}
prop_Insert x (h :: Heap Int) =
  insert x h ==? (x : toList h)

prop_RemoveMin (h :: Heap Int) =
  cover 80 (size h > 1) "non-trivial" $
  case removeMin h of
    Nothing     -> h ==? []
    Just (x,h') -> x == minimum (toList h) && h' ==? (toList h \\ [x])

prop_Merge h1 (h2 :: Heap Int) =
  (h1 `merge` h2) ==? (toList h1 ++ toList h2)

prop_FromList (xs :: [Int]) =
  fromList xs ==? xs

prop_ToSortedList (h :: Heap Int) =
  h ==? xs && xs == sort xs
 where
  xs = toSortedList h

--------------------------------------------------------------------------
-- generators
{- 
instance (Ord a, Arbitrary a) => Arbitrary (Heap a) where
  arbitrary = sized (arbHeap Nothing)
   where
    arbHeap mx n =
      frequency $
        [ (1, return Empty) ] ++
        [ (7, do my <- arbitrary `suchThatMaybe` ((>= mx) . Just)
                 case my of
                   Nothing -> return Empty
                   Just y  -> liftM2 (Node y) arbHeap2 arbHeap2
                    where arbHeap2 = arbHeap (Just y) (n `div` 2))
        | n > 0
        ]
  -}
--------------------------------------------------------------------------
-- main
{- 
return []
main = $quickCheckAll
 -}
--------------------------------------------------------------------------
-- the end.
{-
  shrink Empty          = []
  shrink (Node x h1 h2) =
       [ h1, h2 ]
    ++ [ Node x  h1' h2  | h1' <- shrink h1, x  <=? h1' ]
    ++ [ Node x  h1  h2' | h2' <- shrink h2, x  <=? h2' ]
    ++ [ Node x' h1  h2  | x'  <- shrink x,  x' <=? h1, x' <=? h2 ]
-}

-- toSortedList (Node x h1 h2) = x : toSortedList (h1 `merge` h2)

{-
prop_HeapIsNotSorted (h :: Heap Int) =
  expectFailure $
    toList h == toSortedList h
-}

-- >>>       putStrLn "ciao"
-- >>> prop_Insert 2 (Node 4 Empty Empty)
-- ciao
-- True
--
