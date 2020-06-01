{-# LANGUAGE ScopedTypeVariables, TemplateHaskell #-}
module Lib.QC.Heap where

--------------------------------------------------------------------------
-- imports

import Test.QuickCheck hiding((===))

-- import Data.List
--   ( --sort
--  (\\)
--   )

import Control.Monad
  ( liftM
  , liftM2
  )

import Prelude hiding (length, (++), reverse, iterate, null, splitAt, {- Maybe(..), -} minimum)
import Lib.LH.Prelude
import Language.Haskell.Liquid.ProofCombinators
--------------------------------------------------------------------------
-- skew heaps

{-@ LIQUID "--reflection"    @-}
{-@ LIQUID "--no-termination"    @-} --needed only because of  sweep and toList' 
{-@ LIQUID "--short-names"    @-}
-- {-@ LIQUID "--prune-unsorted"    @-}


-- data Maybe a = Nothing | Just a
--                 deriving (Show, Eq)

-- {-@ data Maybe a = Nothing | Just a @-}
 
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
{-@ reflect unit @-}
unit :: a -> Heap a
unit x = Node x empty empty

{-@ reflect size @-}
size :: Heap a -> Int
size Empty          = 0
size (Node _ h1 h2) = 1 + size h1 + size h2

{-@ reflect insert @-}
insert :: Ord a => a -> Heap a -> Heap a
insert x h = unit x `merge` h

{-@ reflect removeMin @-}
removeMin :: Ord a => Heap a -> Maybe (a, Heap a)
removeMin Empty          = Nothing
removeMin (Node x h1 h2) = Just (x, h1 `merge` h2)


{-@ reflect merge @-}
merge :: Ord a => Heap a -> Heap a -> Heap a
h1    `merge` Empty = h1
Empty `merge` h2    = h2
h1@(Node x h11  h12) `merge` h2@(Node y h21 h22)
  | x <= y    = Node x (h12 `merge` Node y h21 h22) h11
  | otherwise = h2 `merge` h1-- Node y (h22 `merge` Node x h11  h12) h21

-- {-@ reflect fromList @-}
fromList :: Ord a => [a] -> Heap a
fromList xs = merging [ unit x | x <- xs ]
{-@ reflect merging @-}
merging []  = empty
merging [h] = h
merging hs  = merging (sweep hs)
{-@ reflect sweep @-}
sweep []         = []
sweep [h]        = [h]
sweep (h1:h2:hs) = (h1 `merge` h2) : sweep hs

-- {-@ ignore toList @-}
{-@ reflect toList @-}
{-@ toList :: h:Heap a -> [a] @-} --OList a @-}
toList :: Heap a -> [a]
toList h = toList' [h]

{-@ reflect toList' @-}
{-@ toList' :: [Heap a] -> [a] @-} --OList a @-}
toList' :: [Heap a] -> [a]
toList' []                  = []
toList' (Empty        : hs) = toList' hs
toList' (Node x h1 h2 : hs) = x : toList' (h1:h2:hs)

{-@ reflect toSortedList @-}
toSortedList :: Ord a => Heap a -> [a]
toSortedList Empty          = []
toSortedList (Node x h1 h2) = x : toList (h1 `merge` h2)

--------------------------------------------------------------------------
-- specification

{-@ reflect invariant @-}
{-@  invariant ::  Ord a => Heap a -> { v :Bool | v } @-}
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

{-@ reflect prop_Merge @-}
prop_Merge h1 (h2 :: Heap Int) =
  (h1 `merge` h2) ==? (toList h1 ++ toList h2)
