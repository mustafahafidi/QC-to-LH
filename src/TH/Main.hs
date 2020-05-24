{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE  TemplateHaskell #-}
module TH.Main where
    
-- import Lib.LH.Prelude ((++))
-- import Prelude hiding ((++))
import Language.Haskell.TH
import Language.Haskell.Liquid.UX.QuasiQuoter
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Meta.Parse

-- [lq| LIQUID "--reflection" |]
-- {-@ test :: { True } @-}

-- -- {-@  type Unit = ()  @-}
-- -- {-@  type Asd = {v:_ | true}  @-}
-- -- [lq| type Unit1 = () |]
-- -- [lq| type Asd1 = {v:Int | true} |]

-- -- [lq| reflect test |]
-- -- test = [1] ++ [] == [1]




-- ttt::Int
-- ttt = 3

{-======================================================
                        Parse input
=======================================================-}
parsePropName :: String -> Q Info
parsePropName pName = do
                        Just nm <- lookupValueName pName
                        reify nm

{-======================================================
                        entrypoint
=======================================================-}
generateProof :: Q Exp -> Q [Dec]
generateProof exp = do  
                        lhDec   <- (lqDec $ show (mkName "proof") ++ " :: " ++ "Proof")
                        bodyDec <- [d| $(varP $ mkName "proof") = toProof $exp |]
                        return $ lhDec ++ bodyDec

{-======================================================
                        entrypoint String
=======================================================-}
generateProof2 :: String -> Q [Dec]
generateProof2 exp = case parseExp exp of
                            Left err -> fail $ "[qc-to-lh] error: The given expression cannot be parsed"
                            Right parsedExp -> do
                                lhDec   <- (lqDec $ show (mkName "proof") ++ " :: {v:()| " ++ exp ++"}")
                                bodyDec <- [d| $(varP $ mkName "proof") = toProof $(pure parsedExp) |]
                                return $ lhDec ++ bodyDec
                        
