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

-- type Test a = [a]

data Test = Empty
$( return [] )

[lhp|caseExpand
pred2 ::  Int -> Bool -> Bool
pred2 n  b = n
|]


main1 :: IO ()
main1 = putStrLn $(do
        (TyConI (DataD ctx nm tvbndr knd constrs drvcls)) <- reify ''Int
        -- info <- reify $ mkName "Int"
        -- let () = dec
        -- let dataTypestr = map pprint (constrs::[Con])
        reportWarning $ show constrs

        -- let splitted = strSplitAll "|" dataTypestr
        -- reportWarning $ show $ splitted
        stringE ""
        
        )


-- >>> pred2_proof 2 
-- ()
--
