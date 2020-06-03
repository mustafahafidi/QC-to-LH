{-# LANGUAGE  TemplateHaskell #-}
{-# LANGUAGE  QuasiQuotes #-}
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

{-@ ple proof @-}
{-@ proof :: n : N -> { plus Z n = n } @-}
proof :: N -> ()
proof Z     = ()
proof (S n) = () ? proof n

-- automatically by lhp
[lhp|genProp|reflect|ple|caseExpand|induction
property :: N ->  Bool
property z = plus Z z == z
|]
 -}


{-======================================================
            EXAMPLE 2 automatic induction
=======================================================-}

[lhp|genProp|reflect|ple|caseExpand|induction
involution :: [a] -> Bool
involution xs = reverse (reverse xs) == xs
|]