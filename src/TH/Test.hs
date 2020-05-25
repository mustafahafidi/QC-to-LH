{-# LANGUAGE  TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}

module TH.Test where
import TH.Main
import TH.TestProps

import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.TH
import LiquidHaskell
import NeatInterpolation
import Data.Text

-- {-@ LIQUID "--diff" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}


---------------------------------------------------------------
-- Can't get the body of `ttt` because not implemented by GHC
-- http://hackage.haskell.org/package/template-haskell-2.16.0.0/docs/Language-Haskell-TH.html#t:Info
{- 
main :: IO ()
main = putStrLn $(do
        Just nm <- lookupValueName "ttt"
        info <- reify nm
        stringE . show $ info)   
-}
-- >>> main
-- VarI TH.TestProps.ttt (ConT GHC.Types.Int) Nothing
--
----------------------------------------------------------------
-- $(generateProofFromExp [| True == True |]) 
-- this comes as an Q Exp, I need a string to give to lh QQ, showing it gives
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
-- Trying to lookup the info about a binder

-- $(generateProofFromVar $ lookupValueName "testProp1")
-- $(generateProofFromVar $ lookupValueName "asddddd") --no
-- data TestType = Asd
-- $(generateProofFromVar $ lookupValueName "Asd") --no

---------------------------------------------------------------
-- Going the string way
-----------
{-@ reflect asddd @-}
asddd ::   Bool
asddd  =  True

generateProofFromDecl  "asddd :: Bool\n\
                        \asddd = True"
-----------
-- Multiple parameters test
-----------
{-@ reflect testProp1 @-}
testProp1 ::  Bool -> Bool -> Bool
testProp1 x y = True

{-@ ple testProp1_proof  @-}
$(generateProofFromDecl $ "testProp1 ::  Bool -> Bool -> Bool\n\
                          \testProp1 x y = True")

-----------
-- Multiple parameters using multiline QQ
-----------
{-@ reflect testProp2 @-}
testProp2 ::  Bool -> Bool -> Bool
testProp2 x y = (case x of
                    True -> y
                    _    -> False) == (x && y)

{-@ ple testProp2_proof  @-}
generateProofFromDecl $ unpack [text| 
                                        testProp2 ::  Bool -> Bool -> Bool
                                        testProp2 x y = (case x of
                                                            True -> y
                                                            _    -> False) == (x && y)
                               |]

-----------
-- Multiple clauses
-----------
{-@ reflect testProp3 @-}
testProp3 ::  Bool -> Bool
testProp3 True =  True
testProp3 False = True

{-@ ple testProp3_proof  @-}
generateProofFromDecl $ unpack [text| 
                                testProp3 :: Bool -> Bool
                                testProp3 True =  True
                                testProp3 False = True
                               |]
 

-----------
-- Multiple pattern guards
-----------
{-@ reflect testProp4 @-}
testProp4 ::  Int -> Bool
testProp4 x
    | x==0 = True
    | otherwise = True

{-@ ple testProp4_proof  @-}
generateProofFromDecl $ unpack [text| 

testProp4 :: Int -> Bool
testProp4 x
        | x==0 = True
        | otherwise = True 
                               |]


{-@ ttt ::  f:(Bool->Bool) -> {v:_ | f True == f True} @-}
ttt ::  (Bool->Bool) -> Bool
ttt f = True

---------
-- Not supported yet
---------
{-@ reflect testFunctPar @-}
testFunctPar ::  (Bool -> Bool) -> Bool
testFunctPar f = f True == f True

{-@ ple testFunctPar_proof  @-}
generateProofFromDecl $ unpack [text| 

testFunctPar ::  Bool
testFunctPar =  True

                               |]
{- 
Current usage:
  - Parsing signature supports only normal currying (no functions as arguments (e.g. (a->b) -> c))
  - It's possible to refer to the proof name as propertyName_proof. To use local PLE it's possible to use the propertyName_proof
-}



-- {-@ ple testProp1_proof  @-}
-- testlq x = [lq| testProp1_proof :: x:Bool -> y:Bool -> {v:Proof| $x } |]
-- testProp1_proof x y = (True) *** QED












--------------------------------------------------------
{- 
main1 :: IO ()
main1 = putStrLn $(do
        Just nm <- lookupValueName "testProp1"
        info <- reify nm
        stringE . show $ info)

main2 :: IO ()
main2 = putStrLn $(do
            decs <- [d| asd :: Int
                        asd = 3 |]
            stringE (pprint decs)
        ) -}
-- >>> main2
-- 2
--
----------------------------------------------------------------
