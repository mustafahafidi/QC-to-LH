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
-- {-@ LIQUID "--diff" @-}






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

-- [lhp|genProp|reflect|ple|caseExpand|induction
-- propList :: [Int] -> Bool
-- propList ls = ls ==ls
--                 -- ? propList_proof ls
-- |]


-- [lhp|genProp|reflect|ple|caseExpand|induction
-- rightIdP :: Eq a => [a]-> Bool
-- rightIdP xs  = xs ++ [] == xs
-- |]

[lhp|genProp|reflect|ple|caseExpand|inductionP:1
assocP ::  Eq a => [a] -> [a] -> [a] -> Bool
assocP xs ys zs = xs ++ (ys ++ zs) == (xs ++ ys) ++ zs 
|]

-- {-@ rewriteWith distributivityP_proof [rightIdP] @-}
-- [lhp|genProp|reflect|ple|caseExpand|induction:1
-- distributivityP :: Eq a => [a] -> [a] -> Bool
-- distributivityP xs ys = reverse (xs ++ ys) == (reverse ys) ++ (reverse xs)
-- |]
