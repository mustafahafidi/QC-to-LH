{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE  TemplateHaskell #-}
module TH.ProofGenerator (
    generateProofFromDecl,
    generateProofFromExp,
    generateProofFromVar,
    lhp
) where
    
import Language.Haskell.TH
import Language.Haskell.Liquid.UX.QuasiQuoter
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Meta.Parse
import Language.Haskell.TH.Quote
import Control.Monad

import Data.List
import Data.Strings

-- Needed ignores because LH fails with "elaborate elabToInt" on this module
{-@ ignore lhp @-}
{-@ ignore generateProofFromExp @-}
{-@ ignore generateProofFromDecl @-}
{-@ ignore generateProofFromVar @-}
{-@ ignore generateProofFromVar @-}
{-@ LIQUID "--max-case-expand=0" @-}
{-@ LIQUID "--diff" @-}
-- {-@ ignore TH.ProofGenerator @-}

debug = False

-- |
-- A QuasiQuoter that takes the declaration of a 
-- property and generates a proof obligation for it
lhp :: QuasiQuoter
lhp = QuasiQuoter {
    
    quoteExp = bad,
    quotePat = bad,
    quoteType = bad,
    quoteDec = generateProofFromDecl
    }
    where
        bad = error "`lhq` quasiquoter can only be used as a top-level declaration"




-- ======================================================
-- |Given an expression as String, it parses it and 
--  generates a simple proof obligation
-- ======================================================
generateProofFromExp :: String -> Q [Dec]
generateProofFromExp exp = case parseExp exp of
                            Left err -> failWith $ "The given expression cannot be parsed"
                            Right parsedExp -> do
                                pName <- newName "proof"
                                lhDec   <- (lqDec $ show (pName) ++ " :: {v:()| " ++ exp ++"}")
                                bodyDec <- [d| $(varP $ mkName (show pName)) = $(pure parsedExp) ***QED |]
                                return $ lhDec ++ bodyDec


-- ======================================================
-- |Given a function declaration as String, parses it 
-- and generates a proof for it.
-- 
-- If debug=True it will generate warnings with generated refinement types
-- ======================================================
generateProofFromDecl :: String -> Q [Dec]
generateProofFromDecl decs = 
            case parseDecs decs of
                Left err -> failWith $ "The given declaration cannot be parsed: " ++ decs++err
                Right parsedDecls -> do
                    -- checking declarations
                    when (length parsedDecls < 2) (failWith $ "Please provide both type signature and body of the function.")
                    -- getting the signature
                    let (sd:(bodyDs@(bd:bs))) = parsedDecls
                    let (SigD nm sigType) = sd
                    -- reportWarningToUser $ show $ bodyDs
                    -- generate name for the proof
                    let proofName = show nm ++"_proof"
                    -- let sigTypes = strSplitAll "->" $ pprint (SigD (mkName proofName) sigType)
                    -- check that it returns a boolean
                    case isSuffixOf "Bool" (pprint sd) of
                        False -> failWith "The given declaration must return a boolean to be transformed to a LiquidHaskell proof"
                       
                        True  -> do
                          -- (SigD (mkName proofName) sigType)
                                -- add parameters to signature
                                    (typeWP, pr) <- addParamsToType sigType []
                                    -- reportWarningToUser $ show typeWP ++ show pr
                                    let sigTypesWP = strSplitAll "->" $ case typeWP of
                                                                          (ForallT tvb ctx tp) -> pprint tp
                                                                          v -> pprint v
                                    -- reportWarningToUser $ show sigTypesWP
                                -- replace return type with refinement type
                                    let fr = init sigTypesWP --splitAt (length sigTypesWP - 1) sigTypesWP
                                    let params = init pr --splitAt (length pr - 1) pr
                                    let replacedRetTypeSig = (strJoin " -> " $
                                                                    fr ++ ["{v:Proof | "++show nm++" "++(strJoin " " (map (\p->show p) params))++"}"])
                                -- Put back `for all` and context if there was
                                    wildT <- wildCardT
                                    let forAllSig =    (case typeWP of
                                                              ForallT tvb ctx _ -> init $ pprint (ForallT tvb ctx wildT)
                                                              _ -> "")
                                    let finalRefSign = (show $ mkName proofName) ++ " :: "
                                                        ++ forAllSig
                                                        ++ replacedRetTypeSig
                                    when debug $ reportWarningToUser $ "[qc-to-lh]: "++finalRefSign
                                    lhDec <- lqDec finalRefSign
                                -- generate the body
                                    -- add the ***QED to the body for each clause

                                    -- (FunD nm clss)
                                    let finalBody = case bd of
                                                      FunD _ clss -> 
                                                                let proofClss = map  (\(Clause pns body decs) -> (Clause pns (wrapBodyWithProof body) decs)) clss
                                                                in FunD (mkName proofName) proofClss
                                                      ValD _ body decs  -> ValD (VarP (mkName proofName)) (wrapBodyWithProof body) decs
                                    

                                                        
                                    return $ lhDec ++ [finalBody]




-- ======================================================
-- |Given a variable name, tries to lookup its info (using `reify`) 
-- and generate a proof for it
-- ======================================================
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
    
    
-- ======================================================
-- |Find a signature in a list of given declarations    
-- ======================================================
findSignature :: [Dec] -> Q Dec
findSignature decs =  case maybeFound of
                            Nothing -> failWith "Cannot find the signature of the function declaration given"
                            Just dec -> return dec
                where maybeFound = find (\d -> case d of
                                                (SigD _ _) -> True
                                                _ -> False) decs

-- ======================================================
-- |Given a type adds parameters (LH way) and returns the
--  type and the parameters it added
-- ======================================================
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
-- addParamsToType v        = failWith $ "Cannot parse the signature to add LH parameters in it:"++" don't konw how to treat " ++ (show v)

-- ======================================================
-- |Given a function `Body` wraps it to `(Body)***QED`
-- ======================================================
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

-- ======================================================
-- |Report errors  with prefix
-- ======================================================
failWith:: MonadFail m=> String -> m a
failWith message = fail $ "[qc-to-lh] error: "++ message

reportErrorToUser s = reportError $ "[qc-to-lh]: "++s
reportWarningToUser s = reportWarning $ "[qc-to-lh]: "++s