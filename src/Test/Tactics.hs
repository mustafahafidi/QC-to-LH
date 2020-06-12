{-# LANGUAGE  QuasiQuotes #-}
-- {-# OPTIONS_GHC -dth-dec-file #-}
module Test.Tactics where 
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Liquid.ProofGenerator
import Prelude  hiding (length, 
                        (++), 
                        reverse, 
                        iterate, 
                        null, 
                        splitAt,
                        any
                        )
import Lib.LH.Prelude  


{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--shortnames" @-}






{-======================================================
            EXAMPLE 1 automatic induction
=======================================================-}
{-
data NAT = S NAT | Z 
    deriving (Show,Eq)


$(return [])


{-@ reflect plus @-}
plus :: NAT -> NAT -> NAT
plus m Z     = m
plus m (S n) = S (plus m n)

-- normal proof requires inductive hypothesis
{-@ ple proof @-}
{-@ proof :: n : NAT -> { plus Z n = n } @-}
proof :: NAT -> ()
proof Z     = ()
proof (S n) = () ? proof n

 
-- automatically put by lhp
[lhp|genProp|reflect|ple|caseExpand|induction
property :: NAT ->  Bool
property n = plus Z n == n
|]
-}

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


-- lhp does them for you
[lhp|genProp|reflect|ple|caseExpand|induction
rightIdP :: Eq a => [a]-> Bool
rightIdP xs  = xs ++ [] == xs
|]

 

{-======================================================
        Example 3 - limit case expansion and induction
=======================================================-}

-- -- limit the case expansion (thus induction too)
-- [lhp|genProp|reflect|ple|induction|caseExpandP:1
-- assocP ::  Eq a => [a] -> [a] -> [a] -> Bool
-- assocP xs ys zs = xs ++ (ys ++ zs) == (xs ++ ys) ++ zs 
-- |]



-- the limit is vital to prove this
[lhp|genProp|reflect|ple|induction|caseExpandP:2
assoc2 :: Eq a => [a] -> [a] -> [a] -> [a] -> Bool
assoc2 xs ys zs ws = xs ++ (ys ++ (zs ++ ws)) == ((xs ++ ys) ++ zs) ++ ws
|]


