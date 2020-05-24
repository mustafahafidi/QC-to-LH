{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE  TemplateHaskell #-}
module TH.Main where
    
import Language.Haskell.TH
import Language.Haskell.Liquid.UX.QuasiQuoter
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Meta.Parse


{-======================================================
                        entrypoint String
=======================================================-}
generateProof :: String -> Q [Dec]
generateProof exp = case parseExp exp of
                            Left err -> fail $ "[qc-to-lh] error: The given expression cannot be parsed"
                            Right parsedExp -> do
                                pName <- newName "proof"
                                lhDec   <- (lqDec $ show (pName) ++ " :: {v:()| " ++ exp ++"}")
                                bodyDec <- [d| $(varP $ mkName (show pName)) = toProof $(pure parsedExp) |]
                                return $ lhDec ++ bodyDec
                        
