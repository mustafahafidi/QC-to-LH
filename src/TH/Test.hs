{-# LANGUAGE  TemplateHaskell #-}

module TH.Test where
import TH.Main
import TH.TestProps

import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.TH
---------------------------------------------------------------
-- Can't get the body of `ttt` because not implemented by GHC
-- http://hackage.haskell.org/package/template-haskell-2.16.0.0/docs/Language-Haskell-TH.html#t:Info
main :: IO ()
main = putStrLn $(do
        Just nm <- lookupValueName "ttt"
        info <- reify nm
        stringE . show $ info)
-- >>> main
-- VarI TH.TestProps.ttt (ConT GHC.Types.Int) Nothing
--
----------------------------------------------------------------
$(generateProof [| True == True |]) 
-- this comes as an Q Exp, I need a string to give to lhQQ, showing it gives
-- InfixE (Just (ConE GHC.Types.True)) (VarE GHC.Classes.==) (Just (ConE GHC.Types.True))
----------------------------------------------------------------

-- >>> runQ [|2|]
-- LitE (IntegerL 2)
--
