{-# LANGUAGE QuasiQuotes #-}

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

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
-- {-@ LIQUID "--diff" @-}

{-

data CList a = Empty
             | CList [a] a [a]
             deriving (Eq, Show)

{-@ reflect =*= @-}
{-@ infix 4 =*= @-}
(=*=) :: Eq a  => CList a -> CList a -> Bool
a =*= b = (any ((toList a ==) . toList) (toList $ allRotations b))


[lhp|genProp|reflect|ple

lemma_refl :: Eq a => CList a -> Bool
lemma_refl cl@Empty = cl =*= cl
-- lemma_refl cl = cl =*= cl

|]
 -}

-- [lhp|runLiquid|]
-- gdfgfd

[lhp|ple|reflect|genProp|runLiquid

testProp7 :: Bool -> [Bool] -> Bool
testProp7 x y = False
|]

-- [lhp|ple|genProp|runLiquid

-- testProp8 :: Bool -> [Bool] -> Bool
-- testProp8 x (y:ys) = y:[y]==[True]

{- -- |] -}

{- 


{-@ proof_name ::  {False} @-}
proof_name ::  Proof
proof_name = True ***QED


{-@ proof2  ::  {True} @-}
proof2  ::  Proof
proof2  = True ***QED
 -}
{- 
main = putStr "helloworld" -}