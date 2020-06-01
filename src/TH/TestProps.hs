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

-- type Test a = [a]

-- data Test = Empty
-- -- $( return [] )
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


-- main1 :: IO ()
-- main1 = putStrLn $(do
--         (TyConI (DataD ctx nm tvbndr knd constrs drvcls)) <- reify ''Int
--         -- info <- reify $ mkName "Int"
--         -- let () = dec
--         -- let dataTypestr = map pprint (constrs::[Con])
--         reportWarning $ show constrs
--         -- let splitted = strSplitAll "|" dataTypestr
--         -- reportWarning $ show $ splitted
--         stringE ""
--         )
{-@ LIQUID "--shortnames" @-}


-- {-@ reflect pred_Size @-}
-- pred_Size ::  Heap Int -> Bool
-- -- pred_Size h@Empty  = 
-- --   size h == length (toList h)
-- -- pred_Size h@(Node v hl hr)  = 
-- --   size h == length (toList h)
-- pred_Size h = (size h) == length (toList h)
-- -- {-@ rewriteWith prop_Size [distProp, append_length, pred_Size] @-}
-- {-@ ple prop_Size @-}
-- {-@ prop_Size ::  h:Heap Int -> { pred_Size h } @-}
-- prop_Size ::  Heap Int -> Proof
-- -- prop_Size h@Empty  = trivial
-- prop_Size h@(Node v hl hr)  = ((size h) == length (toList h) ? (distProp [hl]) [hr]
--        ? TH.TestProps.prop_Size hl
--        ? TH.TestProps.prop_Size hr
--        ? (append_length (toList' [hl])) (toList' [hr]))
--       *** QED
-- prop_Size h  = ((size h) == length (toList h)) *** QED

-- {-@ LIQUID "--notermination" @-}
-- {-@ LIQUID "--nototality" @-}

{-@ rewriteWith prop_Size_proof [distProp, append_length] @-}
[lhp|genProp|reflect|ple|caseExpand
prop_Size ::  Heap Int -> Bool
prop_Size h@(Node v hl hr)  = size h == length (toList h) 
                ? distProp [hl] [hr]
                ? prop_Size_proof hl
                ? prop_Size_proof hr
                ? append_length (toList' [hl]) (toList' [hr]) 
                
prop_Size h  = size h == length (toList h) 
|]