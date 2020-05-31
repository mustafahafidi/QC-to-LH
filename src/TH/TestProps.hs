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




import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote

import Data.Strings


{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--reflection" @-}
data CList a = Empty
             | CList [a] a [a]
             deriving (Eq, Show)
-- type Test a = [a]

$( return [] )

[lhp|debug|caseExpand
pred2 ::  Bool -> Bool
pred2 n  = n==n
|]

-- main1 :: IO ()
-- main1 = putStrLn $(do
--         (TyConI (DataD ctx nm tvbndr knd constrs drvcls)) <- reify ''Test
--         -- let () = dec
--         let dataTypestr = show $ {- map pprint  -}(constrs::[Con])
--         reportWarning $ dataTypestr

--         -- let splitted = strSplitAll "|" dataTypestr
--         -- reportWarning $ show $ splitted
--         stringE ""
        
--         )


-- >>> pred2_proof 2 
-- ()
--
