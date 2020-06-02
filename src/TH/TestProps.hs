{-# LANGUAGE  TemplateHaskell #-}
{-# LANGUAGE  QuasiQuotes #-}
{-# LANGUAGE  ExplicitForAll #-}
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
import Heap_Proofs



import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote

import Data.Strings


{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--shortnames" @-}

-- type Test a = [a]


-- pp_proof :: Test Int Int -> Proof
-- pp_proof t@Empty = (True) *** QED
-- pp_proof t@(Test _ _) = (True) *** QED



-- [lhp|caseExpand
-- pp :: Test Int Int -> Bool
-- pp t = True
-- |]


-- {-@ infix 4  ++ @-}
-- {-@ rewrite assocP @-}
-- {-@ ple assocP @-}
-- {-@ assocP :: xs:[a] -> ys:[a] -> zs:[a] 
--           -> { xs ++ (ys ++ zs) == (xs ++ ys) ++ zs }  @-}
-- assocP :: [a] -> [a] -> [a] -> Proof
-- assocP [] _ _       = trivial
-- assocP (x:xs) ys zs = assocP xs ys zs
{- 
{-@ reflect pred2 @-}
pred2 :: Eq a => [a] -> [a] -> [a] -> [a] -> Bool
pred2 xs ys zs ws =  xs ++ (ys ++ (zs ++ ws)) == ((xs ++ ys) ++ zs) ++ ws 

{-@ rewriteWith assoc2 [assocP] @-}
{-@ ple assoc2 @-}
{-@ assoc2 :: xs:[a] -> ys:[a] -> zs:[a] -> ws:[a]
          -> { pred2 xs ys zs ws } @-}
assoc2 :: forall a.  Eq a => [a] -> [a] -> [a] -> [a] -> Proof
assoc2 xs ys zs ws
  = (xs ++ (ys ++ (zs ++ ws)) == ((xs ++ ys) ++ zs) ++ ws )
    ***QED

 -}

-- {-@ rewriteWith pred2_proof [assocP] @-}
-- [lhp|genProp|reflect|ple

-- pred2 :: Eq a => [a] -> [a] -> [a] -> [a] -> Bool
-- pred2 xs ys zs ws =  xs ++ (ys ++ (zs ++ ws)) == ((xs ++ ys) ++ zs) ++ ws 

-- |]


-- [lhp|genProp|reflect|ple|caseExpand
-- assoc1 :: Eq a => [a] -> [a] -> [a] -> [a] -> Bool
-- assoc1 (x:xs) ys zs = () ? assoc1_proof xs ys zs
-- assoc1 xs ys zs = xs ++ (ys ++ zs) == (xs ++ ys) ++ zs
-- |]
-- [lhp|caseExpand
-- assoc1 :: Eq a => [a] -> [a] -> Bool
-- assoc1 xs ys  = True
-- |]

-- $( return [] )

data Test = Empty Test | Test 
$( return [] )

-- [lhp|caseExpand
-- p :: Test -> Bool
-- p v = True
-- |]

-- main1 :: IO ()
-- main1 = putStrLn $(do
--         (TyConI (DataD ctx nm tvbndr knd constrs drvcls)) <- reify ''[]
--         -- info <- reify $ ''Test
--         -- let () = dec
--         -- let dataTypestr = map pprint (constrs::[Con])
--         recCons <- getRecursiveConstr (nm,constrs)
--         reportWarning $ show $ recCons
--         -- reportWarning $ show constrs
--         -- let splitted = strSplitAll "|" dataTypestr
--         -- reportWarning $ show $ splitted
--         stringE ""
--         )

