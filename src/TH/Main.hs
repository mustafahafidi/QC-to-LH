{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE  TemplateHaskell #-}
module TH.Main where
    
import Language.Haskell.TH
import Language.Haskell.Liquid.UX.QuasiQuoter
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Meta.Parse
import Control.Monad

import Data.List
import Data.Strings


{-======================================================
                        entrypoint String
=======================================================-}
generateProofFromExp :: String -> Q [Dec]
generateProofFromExp exp = case parseExp exp of
                            Left err -> reportErrorToUser $ "The given expression cannot be parsed"
                            Right parsedExp -> do
                                pName <- newName "proof"
                                lhDec   <- (lqDec $ show (pName) ++ " :: {v:()| " ++ exp ++"}")
                                bodyDec <- [d| $(varP $ mkName (show pName)) = toProof $(pure parsedExp) |]
                                return $ lhDec ++ bodyDec



{-======================================================
                        from var
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
    
    
{-======================================================
                    From decl
=======================================================-}
generateProofFromDecl :: String -> Q [Dec]
generateProofFromDecl decs = 
            case parseDecs decs of
                Left err -> reportErrorToUser $ "The given declaration cannot be parsed: " ++ decs++err
                Right parsedDecls -> do
                    -- checking declarations
                    when (length parsedDecls < 2) (reportErrorToUser $ "Please provide both type signature and body of the function.")
                    -- getting the signature
                    let (sd:(bodyDs@(bd:bs))) = parsedDecls
                    let (SigD nm sigType) = sd
                    -- reportError $ show $ bodyDs
                    -- generate name for the proof
                    let proofName = show nm ++"_proof"
                    -- let sigTypes = strSplitAll "->" $ pprint (SigD (mkName proofName) sigType)
                    -- check that it returns a boolean
                    case isSuffixOf "Bool" (pprint sd) of
                        False -> reportErrorToUser "The given declaration must return a boolean to be transformed to a LiquidHaskell proof"
                       
                        True  -> do
                          -- (SigD (mkName proofName) sigType)
                                -- add parameters to signature
                                    (typeWP, pr) <- addParamsToType sigType []
                                    -- reportError $ show typeWP ++ show pr
                                    let sigTypesWP = strSplitAll "->" $ pprint typeWP

                                -- replace return type with refinement type
                                    let (fr,_) = splitAt (length sigTypesWP - 1) sigTypesWP
                                    let (params,_) = splitAt (length pr - 1) pr
                                    let finalRefType = (show $ mkName proofName) ++ " :: " ++ (strJoin " -> " $
                                                      fr ++ ["{v:Proof | "++show nm++" "++(strJoin " " (map (\p->show p) params))++"}"])
                                    -- reportErrorToUser $ finalRefType
                                    lhDec <- (lqDec finalRefType)
                                -- generate the body
                                    -- add the ***QED to the body for each clause

                                    -- (FunD nm clss)
                                    let finalBody = case bd of
                                                      FunD _ clss -> 
                                                                let proofClss = map  (\(Clause pns body decs) -> (Clause pns (wrapBodyWithProof body) decs)) clss
                                                                in FunD (mkName proofName) proofClss
                                                      ValD _ body decs  -> ValD (VarP (mkName proofName)) (wrapBodyWithProof body) decs
                                    

                                                        
                                    return $ lhDec ++ [finalBody]
                   

findSignature :: [Dec] -> Q Dec
findSignature decs =  case maybeFound of
                            Nothing -> reportErrorToUser "Cannot find the signature of the function declaration given"
                            Just dec -> return dec
                where maybeFound = find (\d -> case d of
                                                (SigD _ _) -> True
                                                _ -> False) decs

-- |Given a signature adds parameters and returns them
-- addParamsToSignature :: Dec -> Q (Dec, [Name])
-- addParamsToSignature (SigD nm sigType) =  do (typeWithParams, params) <-  addParamsToType sigType []
--                                              return ((SigD  nm typeWithParams), params)
--       where
addParamsToType :: Type -> [Name] -> Q (Type, [Name])
addParamsToType (ForallT tvb ctx tp) acc = do (rect, params) <- addParamsToType tp acc
                                              return ((ForallT tvb ctx rect), acc++params)

addParamsToType (AppT t1 t2) acc = do (rect1,p1) <- addParamsToType t1 []
                                      (rect2,p2) <- addParamsToType t2 []
                                      return ((AppT rect1 rect2),acc++p1++p2)

addParamsToType (VarT nm) acc = do nName <- newName "p"
                                   return ((VarT (mkName $ show nName++":"++show nm)), [nName])
addParamsToType (ConT nm) acc = do nName <- newName "p"
                                   return ((ConT (mkName $ show nName++":"++show nm)), [nName])
addParamsToType v acc = return (v, acc)
-- addParamsToType v        = reportErrorToUser $ "Cannot parse the signature to add LH parameters in it:"++" don't konw how to treat " ++ (show v)


wrapBodyWithProof :: Body -> Body
wrapBodyWithProof oldBody@(NormalB bodyExp) = case parseExp $ "(" ++ pprint bodyExp ++ ")***QED" of
                                        Right newBody -> NormalB newBody
                                        Left err -> oldBody

wrapBodyWithProof (GuardedB gds) = GuardedB guards
                                            where
                                                transformBody oldBody = 
                                                  case parseExp $ "(" ++ pprint oldBody ++ ")***QED" of
                                                    Right newBody ->  newBody
                                                    Left err -> oldBody
                                                    
                                                guards = map (\(g, bodyExp) -> (g, transformBody bodyExp)) gds


reportErrorToUser:: MonadFail m => String -> m a
reportErrorToUser message = fail $ "[qc-to-lh] error: "++ message



{- 

Current usage:
  - Parsing signature supports only normal currying (no functions as arguments (e.g. (a->b) -> c))
  - To use local PLE it's possible to use the propertyName_proof
 -}

-- >>> parseExp "  (case x of\n True -> True\n _ -> False)==True"
-- Right (UInfixE (ParensE (CaseE (VarE x) [Match (ConP True []) (NormalB (ConE True)) [],Match WildP (NormalB (ConE False)) []])) (VarE ==) (ConE True))
--
