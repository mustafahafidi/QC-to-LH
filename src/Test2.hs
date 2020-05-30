{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module Test2 where

-- import Lib.QC.Heap (merge, Heap(..))
-- import Prelude hiding (minimum)
-- import Language.Haskell.Liquid.ProofCombinators hiding ((==.))
-- import Test_Heap
import           Lib.LH.Prelude

import           Prelude                                  hiding (any, iterate,
                                                           length, null,
                                                           reverse, splitAt,
                                                           (++))
-- import Lib.QC.Heap (unit, empty, (==?),  toList,toList', invariant, Heap(..), (<=?))
-- import Lib.CL.CircularList

import           Language.Haskell.Liquid.ProofCombinators
import           Language.Haskell.TH.Syntax
import           System.Environment
import           TH.ProofGenerator
import Language.Haskell.Liquid.ProofCombinators
import LiquidHaskell
import Test3
-- import           Lib.CL.CircularList (CList(..))


{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}


-- data CList a = Empty
--              | CList [a] a [a]

{-@ reflect toList @-}
toList :: CList a -> [a]
toList Empty = []
toList (CList l f r) = f : (r ++ (reverse l))


{-@ reflect eqToList @-}
eqToList ::  CList Int -> CList Int -> Bool
eqToList a b = toList a == toList b

{-@ reflect =*= @-}
{-@ infix 4 =*= @-}
(=*=) :: CList Int -> CList Int -> Bool
x =*= y = (any (eqToList x) (toList (singleton y)))

{-@ reflect lemma_refl @-}
lemma_refl :: Bool
lemma_refl = Empty =*= Empty

{-@ ple lemma_refl_proof @-}
{-@ lemma_refl_proof ::  { lemma_refl  } @-}
lemma_refl_proof :: Proof
lemma_refl_proof = lemma_refl
                *** QED


-- {-@ reflect update @-}
-- update :: a -> CList a -> CList a
-- update v Empty = CList [] v []
-- update v (CList l _ r) = CList l v r
