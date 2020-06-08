{-# LANGUAGE  TemplateHaskell #-}
{-# LANGUAGE  QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- {-# OPTIONS_GHC -dth-dec-file #-}
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






{-======================================================
            EXAMPLE 1 automatic induction
=======================================================-}
{-
data NAT = S NAT | Z deriving (Show,Eq)

$(return [])


{-@ reflect plus @-}
plus :: NAT -> NAT -> NAT
plus m Z     = m
plus m (S n) = S (plus m n)

-- -- normal proof requires inductive hypothesis
-- {-@ ple proof @-}
-- {-@ proof :: n : NAT -> { plus Z n = n } @-}
-- proof :: NAT -> ()
-- proof Z     = ()
-- proof (S n) = () ? proof n

-- automatically put by lhp
[lhp|genProp|reflect|ple|caseExpand|induction
property :: NAT ->  Bool
property n = plus Z n == n
|]

-}

{-======================================================
            EXAMPLE 2 automatic induction
=======================================================-}

{- -- Normally the proof requires case distinction and inductive hypothesis
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



[lhp|genProp|reflect|ple|caseExpand|induction
rightIdP :: Eq a => [a]-> Bool
rightIdP xs  = xs ++ [] == xs
|]

 -}

{-======================================================
        Example 3 - limit case expansion and induction
=======================================================-}

{- -- limit the case expansion (thus induction too)
[lhp|genProp|reflect|ple|induction|caseExpandP:1
assocP ::  Eq a => [a] -> [a] -> [a] -> Bool
assocP xs ys zs = xs ++ (ys ++ zs) == (xs ++ ys) ++ zs 
|]

-- the limit is vital to prove this
[lhp|genProp|reflect|ple|induction|caseExpandP:2
assoc2 :: Eq a => [a] -> [a] -> [a] -> [a] -> Bool
assoc2 xs ys zs ws = xs ++ (ys ++ (zs ++ ws)) == ((xs ++ ys) ++ zs) ++ ws
|] -}

{-======================================================
        Example 4
=======================================================-}


-- [lhp|genProp|reflect|ple
-- asd :: Bool
-- asd = 0==2
--     -- ?(0==!1)
-- |]
{- 
{-@ LIQUID "--nototality" @-}
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
 -}


[lhp|genProp|reflect|ple
prop_Size ::  Heap Int -> Bool
prop_Size h@(Node v hl hr)  = ()
                ? distProp [hl] [hr]
                ? prop_Size_proof hl
                ? prop_Size_proof hr
                ? append_length (toList' [hl]) (toList' [hr]) 
                
prop_Size h  = size h == length (toList h) 
|]