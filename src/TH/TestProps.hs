{-# LANGUAGE  TemplateHaskell #-}
{-# LANGUAGE  QuasiQuotes #-}
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
import Lib.CL.CircularList




import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote

import Data.Strings


{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--reflection" @-}

data Test a = Cons1 | Cons2 a

$( return [] )

[lhp|
pred2 :: Test a -> Test a -> Bool
pred2 t1 t2 = True
|]

main1 :: IO ()
main1 = putStrLn $(do
        (TyConI (DataD ctx nm tvbndr knd constrs drvcls)) <- reify ''Test
        -- let () = dec
        let dataTypestr = show $ {- map pprint  -}(constrs::[Con])
        reportWarning $ dataTypestr

        -- let splitted = strSplitAll "|" dataTypestr
        -- reportWarning $ show $ splitted
        stringE ""
        
        )
