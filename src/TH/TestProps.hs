{-# LANGUAGE  TemplateHaskell #-}
{-# LANGUAGE  QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -dth-dec-file #-}
module TH.TestProps where 
import Language.Haskell.Liquid.ProofCombinators
import TH.ProofGenerator
import Prelude  hiding (length, 
                        (++), 
                        reverse, 
                        iterate, 
                        null, 
                        splitAt,
                        any
                        )
import Lib.LH.Prelude  
-- import Lib.CL.CircularList
import Lib.QC.Heap
-- import Heap_Proofs



import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote
import Language.Haskell.Meta.Parse

import Data.Strings


{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--shortnames" @-}





{- [lhp|genProp|reflect|ple|runLiquid
assocP :: Eq a => [a] -> [a] -> [a] -> Bool
assocP (x:xs) ys zs = () ? assocP_proof xs ys zs
assocP xs ys zs = xs ++ (ys ++ zs) == (xs ++ ys) ++ zs
|] -}

-- data T = E T Int | A
-- $(return [])
-- [lhp|genProp|reflect|ple|caseExpand|induction
-- property :: T -> T -> Bool
-- property t v = True
-- |]

{-======================================================
            EXAMPLE 1 automatic induction
=======================================================-}
{- 
data N = S N | Z deriving (Show,Eq)

$(return [])


{-@ reflect plus @-}
plus :: N -> N -> N
plus m Z     = m
plus m (S n) = S (plus m n)

-- normal proof requires inductive hypothesis
{-@ ple proof @-}
{-@ proof :: n : N -> { plus Z n = n } @-}
proof :: N -> ()
proof Z     = ()
proof (S n) = () ? proof n

-- automatically put by lhp
[lhp|genProp|reflect|ple|caseExpand|induction
property :: N ->  Bool
property z = plus Z z == z
|]
 -}


{-======================================================
            EXAMPLE 2 automatic induction
=======================================================-}
{- 
-- Normally the proof requires case distinction and inductive hypothesis
{-@ infix ++ @-}
{-@ ple rightId @-}
{-@ rightId :: xs:[a] -> { xs ++ [] == xs } @-}
rightId :: [a] -> Proof
rightId []     
   =   [] ++ [] 
  === [] 
  *** QED 
rightId (x:xs)
  =   (x:xs) ++ [] 
  === x : (xs ++ [])
      ? rightId xs
  === x : xs
  *** QED

-- lhp proof generator automatically does case splitting and exhaustive induction so with PLE the following is safe:
[lhp|genProp|reflect|ple|caseExpand|induction
rightIdP :: Eq a => [a]-> Bool
rightIdP xs  = xs ++ [] == xs
|]

-}

{-======================================================
        Example 3 GHC lists
=======================================================-}
-- data T = T T | A T

-- [lhp|genProp|reflect|ple|caseExpand|induction
-- propList :: [Int] -> Bool
-- propList ls = ls ==ls
--                 -- ? propList_proof ls
-- |]


-- [lhp|genProp|reflect|ple|caseExpand|induction
-- rightIdP :: Eq a => [a]-> Bool
-- rightIdP xs  = xs ++ [] == xs
-- |]

[lhp|genProp|reflect|ple|caseExpand|induction
assocP ::  Eq a => [a] -> [a] -> [a] -> Bool
assocP xs ys zs = xs ++ (ys ++ zs) == (xs ++ ys) ++ zs 
|]

-- {-@ LIQUID "--nototality" @-}
-- {-@ LIQUID "--no-termination-check" @-}
{- 
{-@ infix ++ @-}
{-@ ple assocP_proof @-}
{-@ assocP_proof :: Eq a => xs:[a] -> ys:[a] -> zs:[a] -> {xs ++ (ys ++ zs) == (xs ++ ys) ++ zs} @-}
assocP_proof :: Eq a => [a] -> [a] -> [a] -> Proof
assocP_proof xs@[] ys@[] zs@[]
  = (xs ++ (ys ++ zs) == (xs ++ ys) ++ zs) *** QED

assocP_proof
  xs@[]
  ys@[]
  zs@(p_4 : p_5)
  = (xs ++ (ys ++ zs) == (xs ++ ys) ++ zs
       ? ((assocP_proof xs) ys) p_5)
      *** QED
assocP_proof
  xs@[]
  ys@(p_2 : p_3)
  zs@[]
  = (xs ++ (ys ++ zs) == (xs ++ ys) ++ zs) *** QED
assocP_proof
  xs@[]
  ys@(p_2 : p_3)
  zs@(p_4 : p_5)
  = (xs ++ (ys ++ zs) == (xs ++ ys) ++ zs
       ? ((assocP_proof xs) p_3) p_5
       ? ((assocP_proof xs) ys) p_5)
      *** QED
assocP_proof
  xs@(p_0 : p_1)
  ys@[]
  zs@[]
  = (xs ++ (ys ++ zs) == (xs ++ ys) ++ zs) 
        ? assocP_proof p_1 ys zs
  *** QED
assocP_proof
  xs@(p_0 : p_1)
  ys@[]
  zs@(p_4 : p_5)
  = (xs ++ (ys ++ zs) == (xs ++ ys) ++ zs)
       ? ((assocP_proof p_1) ys) p_5
       ? ((assocP_proof p_1) ys) zs
       ? ((assocP_proof xs) ys) p_5
      *** QED
assocP_proof
  xs@(p_0 : p_1)
  ys@(p_2 : p_3)
  zs@[]
  = (xs ++ (ys ++ zs) == (xs ++ ys) ++ zs) *** QED
       ? ((assocP_proof p_1) p_3) zs
       ? ((assocP_proof p_1) ys) zs
       ? ((assocP_proof xs) p_3) zs

assocP_proof
  xs@(p_0 : p_1)
  ys@(p_2 : p_3)
  zs@(p_4 : p_5)
  = (xs ++ (ys ++ zs) == (xs ++ ys) ++ zs)
       ? ((assocP_proof p375) p377) p379
       ? ((assocP_proof p375) p377) zs
       ? ((assocP_proof p375) ys) p379
       ? ((assocP_proof p375) ys) zs
       ? ((assocP_proof xs) p377) p379
       ? ((assocP_proof xs) p377) zs
       ? ((assocP_proof xs) ys) p379
       ? ((assocP_proof xs) ys) zs)
      *** QED -}