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
generateProofFromExp :: String -> Q [Dec]
generateProofFromExp exp = case parseExp exp of
                            Left err -> fail $ "[qc-to-lh] error: The given expression cannot be parsed"
                            Right parsedExp -> do
                                pName <- newName "proof"
                                lhDec   <- (lqDec $ show (pName) ++ " :: {v:()| " ++ exp ++"}")
                                bodyDec <- [d| $(varP $ mkName (show pName)) = toProof $(pure parsedExp) |]
                                return $ lhDec ++ bodyDec



{-======================================================
                        entrypoint multiparameter
=======================================================-}
generateProofFromVar :: Q (Maybe Name) -> Q [Dec]
generateProofFromVar varName = 
        do
            mName <- varName
            case mName of
                Just name -> do
                    info <- reify name
                    case info of
                        VarI nm tp mdecl -> fail $ pprint $ tp

                        _                -> fail $ "[qc-to-lh] error: given binder doesn't represent a value variable (" ++ (show name) ++")"
                Nothing -> fail "[qc-to-lh] Cannot find given property name" 
    
    
            {- case parseExp exp of
                            Left err -> fail $ "[qc-to-lh] error: The given expression cannot be parsed"
                            Right parsedExp -> do
                                pName <- newName "proof"
                                lhDec   <- (lqDec $ show (pName) ++ " :: {v:()| " ++ exp ++"}")
                                bodyDec <- [d| $(varP $ mkName (show pName)) = toProof $(pure parsedExp) |]
                                return $ lhDec ++ bodyDec


 -}
-- >>> parseDecs "testProp1 :: Eq a => a -> Bool"
-- Right [SigD testProp1 (ForallT [] [AppT (ConT Eq) (VarT a)] (AppT (AppT ArrowT (VarT a)) (ConT Bool)))]
--
