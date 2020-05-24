{-# LANGUAGE  TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}

module TH.Test where
import TH.Main
import TH.TestProps

import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.TH
import LiquidHaskell

-- {-@ LIQUID "--diff" @-}
{-@ LIQUID "--reflection" @-}


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
-- $(generateProofFromExp [| True == True |]) 
-- this comes as an Q Exp, I need a string to give to lhQQ, showing it gives
-- InfixE (Just (ConE GHC.Types.True)) (VarE GHC.Classes.==) (Just (ConE GHC.Types.True))

----------------------------------------------------------------
-- trying the string way
{-@ reflect testProp @-}
testProp = True == True

-- $(generateProofFromExp "True == True")
-- $(generateProofFromExp "testProp")
-- $(generateProofFromExp "False")
-- $(generateProofFromExp "var = 2")

----------------------------------------------------------------

----------------------------------------------------------------
-- property with parameters
{-@ reflect testProp @-}
-- [lq| testProp1 :: Eq a => a -> {v:Bool | True} |]
testProp1 :: Eq a => a -> Bool -> Bool
testProp1 x y = x == x

$(generateProofFromVar $ lookupValueName "testProp1")


-- $(generateProofFromVar $ lookupValueName "asddddd") --no
-- data TestType = Asd
-- $(generateProofFromVar $ lookupValueName "Asd") --no




main1 :: IO ()
main1 = putStrLn $(do
        Just nm <- lookupValueName "testProp1"
        info <- reify nm
        stringE . show $ info)  

-- >>> main1
-- VarI TH.Test.testProp1 (ForallT [KindedTV a_6989586621679468335 StarT] [AppT (ConT GHC.Classes.Eq) (VarT a_6989586621679468335)] (AppT (AppT ArrowT (VarT a_6989586621679468335)) (AppT (AppT ArrowT (ConT GHC.Types.Bool)) (ConT GHC.Types.Bool)))) Nothing
--
----------------------------------------------------------------
