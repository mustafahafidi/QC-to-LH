{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE  TemplateHaskell #-}
module TH.ProofGenerator 
-- (
--     generateProofFromDecl,
--     generateProofFromExp,
--     lhp
-- )
where
    
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote
import Language.Haskell.Liquid.UX.QuasiQuoter
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Liquid.Liquid

import Language.Haskell.Meta.Parse
import Language.Haskell.Meta.Utils

import Control.Monad
import Control.Applicative
import Control.Exception
import System.IO
import System.Process
import Text.Read

import Data.List
import Data.Strings


import System.Environment



data Option = Ple 
            | Reflect 
            | Ignore 
            | GenProp 
            | Debug 
            | Admit
            | CaseExpand
            | RunLiquid
            | RunLiquidW
            deriving (Eq, Read, Show)

proof_suffix = "_proof"


-- ======================================================
-- |A QuasiQuoter that takes the declaration of a 
-- property and generates a proof obligation for it
-- It accepts the following options:
--   - `ple` generates the ple annotation for *the proof*
--   - `ignore` generates the `ignore` annotation for *the proof*
--   - `reflect` generates the `reflect` annotation for *the property*, works only in conjunction of `genProp`
--   - `genProp` generates the propery along with the proof
--   - `admit` to wrap the proof with "***Admit" instead of "***QED"
--   - `debug` generates a warning containing the generated refinement types & LH annotations
--   - `runLiquid` runs LH locally and silently on the proof (useful with IDE integration)
--   - `runLiquidW` runs LH locally to the proof and shows the result as a warning
--   - `caseExpand` enables case expansion/pattern matching on ADTs
--------------------------------------------------------------
lhp :: QuasiQuoter
lhp = QuasiQuoter {
    
    quoteExp = bad,
    quotePat = bad,
    quoteType = bad,
    quoteDec = parseOptions
    }
    where
        bad = error "`lhq` quasiquoter can only be used as a top-level declaration"


parseOptions :: String -> Q [Dec]
parseOptions str = do
        let (os:bs) = lines $ str
        let body      = strJoin "\n" bs
        opts <- parseGivenOptions (filter (\s->not $ strNull s) (strSplitAll "|" os ))
        

        when (not (elem GenProp opts) &&
              elem Reflect opts ) $ failWith "you cannot use `reflect` without `genProp`"
        generateProofFromDecl body opts

    where
    parseGivenOptions :: MonadFail m => [String] -> m [Option]
    parseGivenOptions [] = return []
    parseGivenOptions (opt:os) =  case (readMaybe . strCapitalize) opt of
                                    Nothing -> failWith $ "Uknown given option `"++opt++"`"
                                    Just opt -> do
                                                rest <- parseGivenOptions os
                                                return (opt:rest)


-- ======================================================
-- |Given a function declaration as String, parses it 
-- and generates a proof for it.
-- ======================================================
generateProofFromDecl :: String -> [Option] ->  Q [Dec]
generateProofFromDecl decs opts = 
    case parseDecs decs of
        Left err -> failWith $ "The given declaration cannot be parsed: " ++ decs++err
        Right parsedDecls -> do
            -- checking declarations
            when (length parsedDecls < 2) (failWith $ "Please provide both type signature and body of the function.")

            -- getting the signature
            let (sd:(bodyDs@(bd:bs))) = parsedDecls
            let (SigD nm sigType) = sd

            -- generate name for the proof
            let proofName = show nm ++proof_suffix
            
            -- check that it returns a boolean
            case isSuffixOf "Bool" (pprint sd) of
                False -> failWith "The given declaration must return a boolean to be transformed to a LiquidHaskell proof"
                True  -> do
            -- Handle options
                let isDebug = elem Debug opts
                optionDecs <- generateFromOptions (show nm) parsedDecls opts 

            -- Transform signature to LH annotation
                lhDec <- transformSignature isDebug sd

            -- Generate the body
                finalBody <- transformBody opts sd bd

            -- Run liquidhaskell locally on binder if asked
                runLiquidHaskell opts (show nm)
                           

                return $ optionDecs ++ lhDec ++ [finalBody]


-- ======================================================
-- |Given the property signature, adds refinement type with parameters
-- and returns corresponding LH annotation
-- ======================================================
transformSignature :: Bool -> Dec -> Q [Dec]
transformSignature isDebug (SigD nm sigType) = do
                let proofName = show nm ++ proof_suffix
            -- add parameters to signature
                (typeWP, pr) <- addParamsToType sigType []

            -- replace return type with refinement type
                let sigTypesWP = strSplitAll "->" typeWP
                let fr = init sigTypesWP --splitAt (length sigTypesWP - 1) sigTypesWP
                let params = init pr --splitAt (length pr - 1) pr
                let replacedRetTypeSig = (strJoin " -> " $
                                                fr ++ ["{v:Proof | "++show nm++" "++(strJoin " " (map (\p->show p) params))++"}"])
            -- Put back `for all` and context if there was
                wildT <- wildCardT
                let forAllSig =    (case sigType of
                                            ForallT tvb ctx _ -> init $ pprint (ForallT tvb ctx wildT)
                                            _ -> "")
                let finalRefSign = (show $ mkName proofName) ++ " :: "
                                    ++ forAllSig
                                    ++ replacedRetTypeSig
                when isDebug $ reportWarningToUser $ finalRefSign
                lqDec finalRefSign


-- ======================================================
-- |Given `lhp` options, signature and body, it generates the proof body
-- ======================================================
transformBody :: [Option] -> Dec -> Dec -> Q Dec
transformBody opts (SigD nm sigType) (FunD _ clss) = do
        let proofName = show nm ++ proof_suffix
        let isAdmit = elem TH.ProofGenerator.Admit opts
        -- if requested generate do case expansion
        pmClss <- if (elem CaseExpand opts) then caseExpandBody sigType (last clss)
                                            else return clss
        let wrap (Clause pns body decs) = Clause pns (wrapBodyWithProof isAdmit body) decs
        let finalProofClss = map wrap (init clss++pmClss)
        return $ FunD (mkName proofName) finalProofClss

transformBody opts (SigD nm sigType) (ValD _ body decs) = do
        let proofName = show nm ++ proof_suffix
        let isAdmit = elem TH.ProofGenerator.Admit opts
        return $ ValD (VarP (mkName proofName)) (wrapBodyWithProof isAdmit body) decs
transformBody _ _ dec = failWith $ "transformBody: Unsupported body declaration: " ++ show dec


                
-- ======================================================
-- |Given the property signature type and a clause of the body,
-- does case expansion (pattern matching on the signature)
-- ======================================================
caseExpandBody :: Type -> Clause -> Q [Clause]
caseExpandBody sigType cls = do
                let paramTypes = init --drop the return type
                            $ strSplitAll "->" 
                            $ pprint
                            $ case sigType of
                                ForallT _ _ tp -> tp 
                                tp             -> tp
                
                -- get the data constructors of the signature types
                constrs <- getConstructors paramTypes
                let signatureConstructors = snd $ unzip constrs
                clss <- patternMatchClauses signatureConstructors cls
                -- exhaustClss <- exhaustiveInduction constrs clss
                -- reportWarningToUser $ show constrs
                -- reportWarningToUser $ show clss
                -- reportWarningToUser $ show exhaustClss
                return clss
   

getName :: Type -> Q Name 
getName (ConT t)   = return t
getName (ListT)   =  return $ mkName "[]"
getName (AppT t _) = getName t
getName v = failWith $ "Cannot get the name of the given type (unsupported): " ++ show v

getConstructors :: [String] -> Q [(Name, [Con])]
getConstructors [] = return []
getConstructors (paramT:pts) = do
    t <- parseGivenType $ paramT
    consName <- getName t
    constrs <- reifyGivenStrType 
                $ show $ consName
    -- failWith $ show $ constrs

    restConstrs <- getConstructors pts
    return $ (consName, constrs) :restConstrs



-- ======================================================
-- |Generates pattern matching given data constructors 
-- and a single declaration clause
-- ======================================================
patternMatchClauses :: [[Con]] -> Clause -> Q [Clause]
patternMatchClauses [] (cls) = return [cls]
patternMatchClauses cons cls@(Clause [] b ds) = return [cls]
patternMatchClauses (cons:cs) (Clause ((VarP nm):vs) b ds) = 
  do
    fpReplaced <- replacePattern cons
    -- given a cls add a parameter to its patterns
    let addParam  p (Clause ptns b ds) = Clause (p:ptns) b ds
    -- "multiplying" single clause to the other pattern matches
    let multiply ((Clause (p:vs) b ds):clss) rest = (map (addParam p) rest) ++ multiply clss rest
        multiply [] rest = []
    restClss <- patternMatchClauses cs (Clause (vs) b ds)
    return $ multiply fpReplaced restClss
    where
        typesToIgnore = ["GHC.Types.I#"] -- don't pattern match on these ones (Int)

        replacePattern [] = return []
        replacePattern ((NormalC nmCons bngs):cs) = do 
                                                        vars <- generateVars bngs
                                                        rest <- replacePattern cs
                                                        return $ ( Clause (AsP nm (ConP nmCons vars):vs) b ds):rest
                                                -- if elem (show nmCons) typesToIgnore
                                                --  then unimplemented
                                                --  else 
        replacePattern ((InfixC bng1 infxCons bng2):cs)  = do 
                                                        (v1:v2:_) <- generateVars [bng1, bng2]
                                                        rest <- replacePattern cs
                                                        return $ ( Clause (AsP nm (InfixP v1 infxCons v2):vs) b ds):rest
        replacePattern (v:cs) = do 
                                    rest <- replacePattern cs
                                    return $ (Clause ((VarP nm):vs) b ds):rest

        generateVars [] = return []
        generateVars (_:bs) = do
                                varName <- newName "p"
                                rest <- generateVars bs
                                return $ (VarP $ mkName $ show varName):rest --the show thing around Name is necessary to keep consistency

        unimplemented = (Clause ((VarP nm):vs) b ds)

patternMatchClauses _ cls = failWith $ "Unimplemented case for pattern matching generation: " ++ pprint cls



-- ======================================================
-- |Given signature constructors, and body adds inductive
-- calls exhaustively on each recursive data type. It should be 
-- called after case expansion (`patternMatchClauses`)
-- ======================================================
-- clause level recursion
exhaustiveInduction :: [(Name,[Con])] -> [Clause] -> Q [([[String]],Clause)]
exhaustiveInduction [] allCases = return [([],cls)|cls<-allCases]
exhaustiveInduction ((nm, con):cons) allCases = do
                                    -- take off one argument and do exhaustive induction recursively
                                    rest <- exhaustiveInduction cons [ (Clause (tail ptns) b d)  | (Clause ptns b d) <- allCases]

                                    recBangs <- getRecursiveConstr nm con
                                    -- put it back on recursive result and add current argument
                                    current <- addInductiveCall (zip con recBangs) allCases

                                    let addParam p ys = p ++ ys
                                    -- "multiplying" single clause to the other pattern matches
                                    let multiply (p:ps) ys = (map (addParam p) ys) ++ multiply ps ys
                                        multiply [] ys = []


                                    let finalClss = [
                                              ind1++ind2
                                            | ( (ind1, c1@(Clause _ _ _)),(ind2, Clause _ _ _) ) <- zip current rest]
                                    reportWarningToUser $ "Current: " ++ (show $ length current)
                                    reportWarningToUser $ "rest: " ++ (show $ length rest)
                                    reportWarningToUser $ "finalClss: " ++ (show $ length finalClss)
                                    reportWarningToUser $ "final: " ++ show finalClss
                                    -- -- failWith $ show $ zip con recBangs
                                    -- -- let (hd) = asd
                                    -- failWith $ show [ strs | (strs,cls) <- finalClss]
                                    return current


--  bang level
addInductiveCall :: [(Con, [Int])] -> [Clause] -> Q [([[String]],Clause)]
-- addInductiveCall [] c = return 
-- addInductiveCall ((_,[]):cs) allCases = return [([],cls)|cls<-allCases] -- if the data cons is not recursive we don't do anything
addInductiveCall ((NormalC nmCons bngs,bis):cs) allCases = do
                                    rest <- addInductiveCall cs allCases --[ (Clause ptns b d)  | (Clause (p:ptns) b d) <- allCases]

                                    -- let (Clause (p:p2:ptns) b d) = head allCases
                                    -- let first   = getProofParam p bis
                                    -- let second   = getProofParam p2 bis
                                    reportWarningToUser $ "addinductivecall" ++ show rest
                                    -- failWith $ show (multiply first second)
                                    -- failWith $ show ([
                                                
                                    --             (multiply pInd (getProofParam p bis) ,
                                    --           Clause p1 b d)
                                    --         | (Clause p1@(p:ptns) _ _,(pInd, Clause _ b d) ) <- zip allCases rest])

                                    return [
                                              ({- multiply -} (getProofParam p bis) ++ pInd ,
                                              (Clause p1 b d)) 
                                            | (Clause p1@(p:ptns) _ _,(pInd, Clause _ b d) ) <- zip allCases rest]
                                    

                                
                                        where
                                            patternUsesRecCons (AsP _ (ConP conPtn ptns)) = normaliseName conPtn == normaliseName nmCons

                                            getProofParam :: Pat -> [Int] -> [[String]]
                                            getProofParam p@(AsP nm (ConP _ (ptns))) ids = 
                                                [  [(if patternUsesRecCons p
                                                        then (ptnToName $ ptns !! i)
                                                        else show nm)]    | i <- ids]
                                                    
                                            ptnToName (VarP nmv) = show nmv

                                            multiply :: [[String]] -> [[String]] -> [[String]]
                                            multiply [] vs = vs
                                            multiply (x:xs) vs = [ x++v | v <- vs] ++ multiply xs vs

                                            -- getIndExp _ [] body = body
                                            -- getIndExp ptns (idx:bs) body 
                                            --         = getIndExp ptns bs newBody
                                            --               where
                                            --                indExp = case parseExp (genProofCall ptns idx) of
                                            --                     Right exp -> exp
                                            --                     _         -> VarE $ mkName "Error"

                                            --                --AppE (VarE $ mkName "proofNameTODO") 
                                            --                newBody = wrapBodyWith (\b -> (UInfixE (b) (VarE $ mkName "?") (indExp))) body
                               
addInductiveCall [] allCases = return [([],cls)|cls<-allCases]                            
addInductiveCall cons clss = failWith $ "Unimplemented case in exhaustive induction : " ++ show cons ++ show clss
    

    
getRecursiveConstr :: Name -> [Con] -> Q [[Int]]
getRecursiveConstr nm [] = return []
getRecursiveConstr nm ((NormalC nmCons bngs):cs) = do   rest <- getRecursiveConstr nm cs
                                                        foundBangs <- (searchInBang nm bngs 0) 
                                                        -- reportWarningToUser $ show $ "found" ++ show (foundBangs:rest)
                                                        return (foundBangs:rest)
getRecursiveConstr nm (_:cs) = failWith $ "Cannot get recursive parts of given type " ++ show nm --Nothing : getRecursiveConstr (nm,cs)
                   

-- says whether the bangs of a single data constructor are recursive
searchInBang :: Name -> [BangType]  -> Int -> Q ([Int])
searchInBang nm ((b,(AppT t1 t2)):bs) idx = do
                                                rest <- searchInBang nm bs (idx+1)
                                                b1 <- searchInBang nm ((b,t1):bs) idx
                                                b2 <- searchInBang nm ((b,t2):bs) idx
                                                -- res <- do bngT1 <|> bngT2
                                                reportWarningToUser $ (show b1 ++ show b2)
                                                
                                                return $ (b1++b2++rest)
searchInBang nm ((b,(ConT nc)):bs) idx = do
                                    rest <- searchInBang nm bs (idx+1)
                                    let isCurrentRec = normaliseName nc == normaliseName nm
                                    -- reportWarningToUser $ (show $  isCurrentRec)
                                    
                                    return $ (if isCurrentRec then [idx] else [])++rest
searchInBang nm [] idx = return []
searchInBang nm v  idx = failWith $ "searchInBang unimplemented given bang: "++show v

-- ======================================================
-- |Run Liquid and return result
-- ======================================================
runLiquidHaskell :: [Option] -> String ->  Q ()
runLiquidHaskell opts propName = do
        -- to avoid loop running liquidhaskell, we set an env variable
        lenv <- runIO $ lookupEnv "lhp-running"
        let isRunning = case lenv of
                            Just "True" -> True
                            _           -> False   
        let shouldRunLqW = elem RunLiquidW opts
        let shouldRunLq = elem RunLiquid opts
        let proofName = propName ++ proof_suffix
        -- error $ "isRunning: " ++ show isRunning
        
        when ((shouldRunLq || shouldRunLqW) && not isRunning) $ do
            spliceLocation <- location
            res <- runIO $ do
                    setEnv "lhp-running" "True"
                    argss <- getArgs
                    let includeArgs = filter (\s->strStartsWith s "-i") argss
                    -- putStrLn $ "argsssss"++show includeArgs
                    -- error $ "isRunning: " ++ show isRunning
                    

                    let liquidArgs = (includeArgs++[
                                    "--check-var", proofName,
                                    "--check-var", propName,
                                    "--no-check-imports",
                                    loc_filename spliceLocation
                                    ])


                    -- -- RUNNING through CLI
                    -- (_, output, _) <- readProcessWithExitCode "liquid" 
                    --                 liquidArgs ""
                    let output = "asd"
                    -- RUNNING through Language.Haskell.Liquid.Liquid 
                    catch (liquid liquidArgs) (\e -> putStrLn (show (e::SomeException)))
                    

                    setEnv "lhp-running" "False"
                    -- indent the output
                    return $ strJoin "  \n   " $ 
                            lines  $
                            last $ strSplitAll "RESULT:" $
                            output

            when (shouldRunLqW) $ 
                reportWarningToUser $  "Result liquidhaskell on: "++ proofName ++  res ++ " \n  "

                                            

-- ======================================================
-- |Given the property declaration, generates additional declarations/annotations that depend on the options 
-- passed to the quasiquoter
-- ======================================================
generateFromOptions :: String -> [Dec] -> [Option] -> Q [Dec]
generateFromOptions _  _  [] = return []
generateFromOptions _  _  [Debug] = return []
generateFromOptions pn pd (Debug:os:oss)   = generateFromOptions pn pd (os:Debug:oss) --need to preserve it
generateFromOptions pn pd (Ple:os) =  boilerplate pn pd os ("ple " ++ pn++proof_suffix)
generateFromOptions pn pd (Ignore:os) = boilerplate pn pd os ("ignore " ++ pn++proof_suffix)
generateFromOptions pn pd (Reflect:os) = boilerplate pn pd os ("reflect " ++ pn)

generateFromOptions pn pd (GenProp:os)   = do   restDecs <- generateFromOptions pn pd os
                                            --   failWith $ show $ map pprint (cleanProof pd)
                                            -- extract only the property (supposed to be given as the last one)
                                                let sign = head pd
                                                let lastDec = case last pd of
                                                                FunD nm clss -> FunD nm [last clss]
                                                                v            -> v
                                                return (restDecs++(cleanProof [sign, lastDec]))

generateFromOptions pn pd (opt:os) =  generateFromOptions pn pd os
                                    -- boilerplate pn pd os ((strToLower $ show opt) ++ " " ++ pn)

boilerplate pn pd os refTypeStr = do
                                    when (elem Debug os) (reportWarningToUser refTypeStr)
                                    lhdec <- lqDec refTypeStr
                                    rest <- generateFromOptions pn pd os
                                    return  (lhdec ++ rest)
    

-- ======================================================
-- |Given a proof, extracts the property (deletes inductive calls made using `?`)
--  This is used to extract the plain property out of a proof
-- ======================================================
cleanProof :: [Dec] -> [Dec]
cleanProof [] = []
cleanProof ((ValD p body decs):rest) = (ValD p (trimInductiveCalls body) decs):(cleanProof rest)
                                    
cleanProof ((FunD nm clss):rest) = (FunD nm (recClean clss)):(cleanProof rest)
                    where
                        recClean [] = []
                        recClean ((Clause p body ds):cls) = (Clause p (trimInductiveCalls body) ds) : recClean cls
cleanProof (v:vs) = v:(cleanProof vs)

trimInductiveCalls :: Body -> Body
trimInductiveCalls (GuardedB grds) = GuardedB (recDelete grds)
                                where
                                    recDelete [] = []
                                    recDelete ((grd, exp):gs) = (grd, deleteInd exp):(recDelete gs)
trimInductiveCalls (NormalB exp) = NormalB (deleteInd exp)
 
deleteInd :: Exp -> Exp
deleteInd old@(UInfixE e1 (VarE op) e2) = case show op of
                                            "?" -> deleteInd e1
                                            _ -> (UInfixE (deleteInd e1) (VarE op) (deleteInd e2))
deleteInd v = v

-- ======================================================
-- |Given a type adds parameters (LH way) and returns the
--  type and the parameters it added
-- ======================================================
addParamsToType :: Type -> [Name] -> Q (String, [Name])
addParamsToType (ForallT tvb ctx tp) acc =  addParamsToTypeStr (pprint tp) []
addParamsToType (tp) acc =  addParamsToTypeStr (pprint tp) []
addParamsToTypeStr :: String -> [Name] -> Q (String, [Name])
addParamsToTypeStr [] _ = return ("",[])
addParamsToTypeStr tp acc = do let (p,ps) = strSplit "->" tp
                               nName <- newName "p"
                               (restWP,addedNames) <- addParamsToTypeStr ps []
                               let finalParts = (show nName ++ ':':p) : filter (not . strNull) [restWP]
                               return (strJoin "->" finalParts,nName:addedNames)



-- ======================================================
-- |Given a Bool `isAdmit` function's `Body` wraps it to `(Body)***QED`
--  or `(Body)***Admit` depending on `isAdmit`
-- ======================================================
wrapBodyWithProof :: Bool -> Body -> Body
wrapBodyWithProof isAdmit oldBody = wrapBodyWith transformExp  oldBody
            where
              typeProof = (if isAdmit then "Admit" else "QED")
              transformExp oldBody = (UInfixE (ParensE (oldBody)) (VarE $ mkName "***") (ConE $ mkName typeProof))



-- ======================================================
-- |Given an expression transformer, applies it on a given Body
-- ======================================================
wrapBodyWith :: (Exp -> Exp) -> Body -> Body
wrapBodyWith transformer oldBody = case oldBody of
                                        NormalB bodyExp -> NormalB $ transformExp bodyExp
                                        GuardedB gds    -> GuardedB (mapGuards gds)
            where
              mapGuards gds = map (\(g, bodyExp) -> (g, transformExp bodyExp)) gds
              transformExp oldBody = transformer oldBody


-- ======================================================
-- |Given type name it attempts to reify it and gets its info 
-- for pattern matching
-- ======================================================
reifyGivenStrType :: String -> Q [Con]
reifyGivenStrType strType = do  info <- reify $ mkName strType
                                supportedType info
    where
        -- supportedType (TyConI (DataD _ _ _ _ constrs _)) = return constrs
        supportedType (TyConI (DataD _ _ _ _ constrs _)) = return constrs
        supportedType _ = failWith "Unsupported given type for pattern matching"


-- ======================================================
-- |Attempts to parse a given type
-- ======================================================
parseGivenType :: String -> Q Type
parseGivenType strType = okOrFail $ parseType strType
            where
                okOrFail (Right t) = return t
                okOrFail _         = failWith $ "Unsupported given type "++strType








-- ====================================UTILITIES=================================



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
-- |Report errors  with prefix
-- ======================================================
failWith:: MonadFail m=> String -> m a
failWith message = fail $ "[qc-to-lh] error: "++ message

reportErrorToUser s = reportError $ "[qc-to-lh]: "++s
reportWarningToUser s = reportWarning $ "[qc-to-lh]: "++s