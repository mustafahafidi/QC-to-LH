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


{-======================================================
            EXAMPLE 2 automatic induction
=======================================================-}

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



{-======================================================
        Example 3
=======================================================-}

-- limit the case expansion (thus induction too)
[lhp|genProp|reflect|ple|induction|caseExpandP:1
assocP ::  Eq a => [a] -> [a] -> [a] -> Bool
assocP xs ys zs = xs ++ (ys ++ zs) == (xs ++ ys) ++ zs 
|]

-- the limit is vital to prove this
-- {-@ rewriteWith assoc2_proof [assocP] @-}
[lhp|genProp|reflect|ple|induction|caseExpandP:2
assoc2 :: Eq a => [a] -> [a] -> [a] -> [a] -> Bool
assoc2 xs ys zs ws = xs ++ (ys ++ (zs ++ ws)) == ((xs ++ ys) ++ zs) ++ ws
|]