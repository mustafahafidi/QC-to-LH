{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE  TemplateHaskell #-}
{-@ LIQUID "--compilespec" @-}
module Language.Haskell.Liquid.ProofGenerator 
(
    generateProofFromDecl,
    generateProofFromExp,
    lhp
)
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
            | Inline 
            | Ignore 
            | GenProp 
            | Debug 
            | Admit
            | CaseExpand
            | CaseExpandP Int
            | Induction
            | InductionP Int
            | RunLiquid
            | RunLiquidW
            deriving (Eq, Read, Show)

type IndParam = (Bool, String) -- the boolean indicates if the parameter is decreasing

proof_suffix = "_proof"


-- ======================================================
-- |A QuasiQuoter that takes the declaration of a 
-- property and generates a proof obligation for it
-- It accepts the following options:
--   - `ple` generates the ple annotation for *the proof*
--   - `ignore` generates the `ignore` annotation for *the proof*
--   - `inline` generates the `inline` annotation for *the property*, works only in conjunction of `genProp`
--   - `reflect` generates the `reflect` annotation for *the property*, works only in conjunction of `genProp`
--   - `genProp` generates the propery along with the proof
--   - `admit` to wrap the proof with "***Admit" instead of "***QED"
--   - `debug` generates a warning containing the generated refinement types & LH annotations
--   - `runLiquid` runs LH locally and silently on the proof (useful with IDE integration)
--   - `runLiquidW` runs LH locally to the proof and shows the result as a warning
--   - `caseExpand` enables case expansion/pattern matching on ADTs
--   - `caseExpandP:{n}` limits the case expansion to the first {n} parameters
--   - `inductionP:{n}` limits the inductive calls to the first {n} parameters
--------------------------------------------------------------
lhp :: QuasiQuoter
lhp = QuasiQuoter {
    
    quoteExp = bad,
    quotePat = bad,
    quoteType = bad,
    quoteDec = parseOptions
    }
    where
        bad = error "`lhp` quasiquoter can only be used as a top-level declaration"


parseOptions :: String -> Q [Dec]
parseOptions str = do
        let (os:bs) = lines $ str
        let body      = strJoin "\n" bs
        opts <- parseGivenOptions (filter (\s->not $ strNull s) (strSplitAll "|" os ))
        

        when (not (elem GenProp opts) 
            && (elem Reflect opts 
              || elem Language.Haskell.Liquid.ProofGenerator.Inline opts)) $ failWith "you cannot use `reflect` or `inline` without `genProp`"
        generateProofFromDecl body opts

    where
    parseGivenOptions :: MonadFail m => [String] -> m [Option]
    parseGivenOptions [] = return []
    parseGivenOptions (opt:os) =  case (readMaybe . strCapitalize .  strReplace ":" " ") opt of
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
            -- failWith $ show $ bodyDs
            -- generate name for the proof
            let proofName = show nm ++proof_suffix
            
            -- check that it returns a boolean
            case isSuffixOf "Bool" (pprint sd) of
                False -> failWith "The given declaration must return a boolean to be transformed to a LiquidHaskell proof"
                True  -> do
                -- Handle options
                    optionDecs <- generateFromOptions (show nm) parsedDecls opts 

                -- Transform signature to LH annotation
                    lhDec <- transformSignature opts sd bd

                -- Generate the body
                    finalBody <- transformBody opts sd bd

                -- Run liquidhaskell locally on binder if asked
                    runLiquidHaskell opts (show nm)
                            

                    return $ optionDecs ++ lhDec ++ [finalBody]


-- ======================================================
-- |Given the property signature, adds refinement type with parameters
-- and returns corresponding LH annotation
-- ======================================================
transformSignature :: [Option] -> Dec -> Dec -> Q [Dec]
transformSignature opts (SigD nm sigType) bd = do
                let proofName = show nm ++ proof_suffix

            --  getting the property and params used
                let inclProp = not $ elem GenProp opts

                extParams <- if inclProp then do (nps,_) <- getProperty bd
                                                 return nps
                                          else return []

            -- add parameters to signature
                (typeWP, pr) <- addParamsToType sigType extParams

            -- replace return type with refinement type
                let sigTypesWP = strSplitAll "->" typeWP
                let fr = init sigTypesWP --splitAt (length sigTypesWP - 1) sigTypesWP
                let params = init pr --splitAt (length pr - 1) pr

                refPredicate <- if inclProp 
                                   then do
                                        (_,pureProperty) <- getProperty bd
                                        return $ pprint pureProperty
                                   else return $ show nm++" "++(strJoin " " (map (\p-> nameToSmallStr p) params))
                
                let replacedRetTypeSig = (strJoin " -> " $
                                                fr ++ ["{v:Proof | "++refPredicate++"}"])
                -- failWith $ replacedRetTypeSig
            -- Put back `for all` and context if there was any
                wildT <- wildCardT
                let forAllSig =    (case sigType of
                                            ForallT tvb ctx _ -> init $ pprint (ForallT tvb ctx wildT)
                                            _ -> "")
                let finalRefSign = (show $ mkName proofName) ++ " :: "
                                    ++ forAllSig
                                    ++ replacedRetTypeSig
                when (elem Debug opts) $ reportWarningToUser $ finalRefSign
                lqDec finalRefSign
        where 
              getProperty (ValD pat bd decs) = 
                                            case bd of
                                                NormalB exp -> return ([], exp)
                                                _ -> failWith $ "unimplmented conversion of guarded body to ref.type expression"
                
              getProperty (FunD _ clss) = do
                                            let (Clause ptns (bd) decs) =  last clss
                                            vars <- getVars ptns
                                            case bd of
                                                NormalB exp -> return (vars, exp)
                                                _ -> failWith $ "unimplmented conversion of guarded body to ref.type expression (use genProp option)"
              getProperty _ = failWith $ "unimplemented: cannot extract pure property"
              getVars [] = return []
              getVars ((VarP nm):rest) = do rs <- getVars rest
                                            return $ nm:rs
              getVars ((WildP):rest) = failWith $ "unsupported: given wildcard in parameter (use genProp option)"

transformSignature _ _ _ = failWith "Not given a signature"


-- ======================================================
-- |Given `lhp` options, signature and body, it generates the proof body
-- ======================================================
transformBody :: [Option] -> Dec -> Dec -> Q Dec
transformBody opts (SigD nm sigType) (FunD _ clss) = do
        let proofName = show nm ++ proof_suffix
        let isAdmit = elem Language.Haskell.Liquid.ProofGenerator.Admit opts
        -- if requested generate do case expansion
        pmClss <-  caseExpandBody proofName opts sigType (last clss) 
        -- if (elem CaseExpand opts) then caseExpandBody sigType (last clss)
        --                                     else return clss
        let wrap (Clause pns body decs) = Clause pns (wrapBodyWithProof isAdmit body) decs
        let finalProofClss = map wrap (init clss++pmClss)
        return $ FunD (mkName proofName) finalProofClss

transformBody opts (SigD nm sigType) (ValD _ body decs) = do
        let proofName = show nm ++ proof_suffix
        let isAdmit = elem Language.Haskell.Liquid.ProofGenerator.Admit opts
        return $ ValD (VarP (mkName proofName)) (wrapBodyWithProof isAdmit body) decs
transformBody _ _ dec = failWith $ "transformBody: Unsupported body declaration: " ++ show dec


                
-- ======================================================
-- |Given the property signature type and a clause of the body,
-- does case expansion (pattern matching on the signature)
-- ======================================================
caseExpandBody :: String -> [Option] -> Type -> Clause -> Q [Clause]
caseExpandBody proofName opts sigType cls = do
            let indPOpt = [opt | opt@(InductionP n) <- opts, n>0]
            let csPOpt = [opt | opt@(CaseExpandP n) <- opts, n>0]
            let mustCaseExpand = elem CaseExpand opts || length csPOpt > 0
            let mustDoInduction = elem Induction opts || length indPOpt > 0

            if (mustCaseExpand) then do
                let paramTypes = init --drop the return type
                            $ strSplitAll "->" 
                            $ pprint
                            $ case sigType of
                                ForallT _ _ tp -> tp 
                                tp             -> tp
                
                expandParamsN <-  case csPOpt of
                                        (CaseExpandP n:_) -> do
                                            when (n>length paramTypes) $ failWith "The given caseExpand parameter is greater than the number of the actual parameters of your proof"
                                            return n
                                        _ -> return $ length paramTypes

                -- get the data constructors of the signature types
                constrs <- getConstructors paramTypes
                let signatureConstructors = snd $ unzip constrs
                clss <- patternMatchClauses expandParamsN signatureConstructors cls

                -- do the induction thing
                if mustDoInduction then do
                    indClauses <- exhaustiveInduction constrs clss
                    -- delete possible non terminating calls
                    let termCallsCls = [ (filterNonTerminatingIndCalls calls, clause) | (calls, clause) <- indClauses]

                    -- limit calls to n-th parameter
                    finalCalls <- case indPOpt of
                                        (InductionP n:_) -> do
                                            when (n>length paramTypes) $ failWith "The given induction parameter is greater than the number of the actual parameters of your proof"
                                            return [(filterNonTerminatingIndCalls $ filterIndCallsToParam n indCalls,cls) | (indCalls, cls) <- termCallsCls ]
                                        _                -> return termCallsCls
                    addInductiveCallsToClauses proofName finalCalls
                else
                    return clss

            else do
                when mustDoInduction $ reportWarningToUser "The `induction` option has no effect without caseExpansion"
                return [cls]
                -- reportWarningToUser $ show constrs
                -- reportWarningToUser $ show clss
                -- reportWarningToUser $ show exhaustClss
                -- return clss
   

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

filterIndCallsToParam :: Int -> [[IndParam]] -> [[IndParam]]
filterIndCallsToParam _ [] = []
filterIndCallsToParam 0 v@([]:_) = v
filterIndCallsToParam 0 indCalls =
    
    let
        rest = filterIndCallsToParam 0 [ ps | ((False,nmp):ps) <- indCalls]
        currentNonRec = nub [  [p] | (p@(False,nmp):_) <- indCalls]
    in  nub $ multiplyHead currentNonRec rest

filterIndCallsToParam n indCalls = 
    let
        rest = filterIndCallsToParam (n-1) [ ps | (pm:ps) <- indCalls]
        currentParams = nub [ [callParam] | ((callParam):csp) <- indCalls]
    in  nub $ multiplyHead currentParams rest


filterNonTerminatingIndCalls :: [[IndParam]] -> [[IndParam]]
filterNonTerminatingIndCalls [] = [] 
filterNonTerminatingIndCalls (indCall : ic) = 
    if(length [()|(True,_) <- indCall] > 0) then
        indCall : filterNonTerminatingIndCalls ic
    else
        filterNonTerminatingIndCalls ic

addInductiveCallsToClauses :: String -> [([[IndParam]], Clause)] -> Q [Clause]
addInductiveCallsToClauses pn [] = return []
addInductiveCallsToClauses pn ((indCalls, (Clause ptns body decs)):cs) = do
                    rest <- addInductiveCallsToClauses pn cs
                    indCallsExps <- generateCalls pn indCalls
                    let newBody = wrapBodyWithIndCalls body indCallsExps
                    return ((Clause ptns newBody decs):rest)
-- ======================================================
-- |Given a Body and a list of expressions, wraps the body 
-- recursively with the `?` proof combinator
-- ======================================================
wrapBodyWithIndCalls :: Body -> [Exp] -> Body
wrapBodyWithIndCalls bd [] = bd
wrapBodyWithIndCalls bd (call:cs) = wrapBodyWith (\b -> (UInfixE (b) (VarE $ mkName "?") (call))) (wrapBodyWithIndCalls bd cs)

-- ======================================================
-- |Given a proof name and a list of inductive calls (only their parameters),
--  returns a list of `proof_name [params..]` call expressions
-- ======================================================
generateCalls :: String -> [[IndParam]] -> Q [Exp] 
generateCalls proofName [] = return []
generateCalls proofName (callParams:cs) = do
            let strCall = strJoin " " (proofName:[ ps | (b,ps) <- callParams])
            rest <- generateCalls proofName cs
            case parseExp strCall of
                Right exp -> return (exp : rest)
                Left err  -> failWith $ "Cannot generate inductive calls: " ++ err
            
 
-- ======================================================
-- |Given signature constructors and body, returns for each clause
-- the inductive calls (only their parameters)
-- ======================================================
exhaustiveInduction :: [(Name,[Con])] -> [Clause] -> Q [([[IndParam]],Clause)]
exhaustiveInduction [] allCases = return [([],cls)|cls<-allCases]
exhaustiveInduction params@(cr@(nm, con):cons) allCases = do
                                    -- take off one argument and do exhaustive induction recursively
                                    rest <- exhaustiveInduction cons [ (Clause (tail ptns) b d)  | (Clause ptns b d) <- allCases]
                                    -- reportWarningToUser $ "calling getRecursiveContrs" ++ show con
                                    recBangs <- getRecursiveConstr nm con
                                    -- failWith $ show $ allCases

                                    -- put it back on recursion result and add current argument
                                    current <- recursiveBangsInd (zip con recBangs) allCases

                                    let finalClss = [
                                              (nub $ multiplyHead ind1 ind2,c1)
                                            | ( (ind1, c1@(Clause _ _ _)),(ind2, Clause _ _ _) ) <- zip current rest]
                                    -- reportWarningToUser $ "params: " ++ (show cr)
                                    -- reportWarningToUser $ "finalClss: " ++ (show $ [(filterNonTerminatingIndCalls calls, pprint cls)|(calls, cls)<-finalClss])
                                    -- reportWarningToUser $ "finalClss2: " 
                                    --     ++ (show $ strJoin "\n"
                                    --         [  show $ multiply ind1 ind2 | ( (ind1, c1@(Clause _ _ _)),(ind2, Clause _ _ _) ) <- zip current rest])
                                    return finalClss
                           

--  generates inductive call within a single type (its constructors are given)
recursiveBangsInd :: [(Con, [Int])] -> [Clause] -> Q [([[IndParam]],Clause)]
recursiveBangsInd [] allCases = return [([],cls)|cls<-allCases]                            
recursiveBangsInd ((cr,bis):cs) allCases 
                | (NormalC nmCons bngs) <- cr = do
                                    rest <- recursiveBangsInd cs allCases 
                                    let final  = [
                                              ((getIndCallParams nmCons p bis) ++ pInd,
                                              (Clause p1 b d)) 
                                            | (Clause p1@(p:_) _ _,(pInd, Clause _ b d) ) <- zip allCases rest]
                                   
                                    return final
                                
                | (InfixC bngt1 nmCons bngt2) <- cr = do
                                    rest <- recursiveBangsInd cs allCases 
                                    let final  = [
                                              ((getIndCallParams nmCons p bis) ++ pInd,
                                              (Clause p1 b d)) 
                                            | (Clause p1@(p:_) _ _,(pInd, Clause _ b d) ) <- zip allCases rest]
                                   
                                    return final

                            where
                                            

                                getIndCallParams :: Name -> Pat -> [Int] -> [[IndParam]]
                                getIndCallParams nmCons (AsP nm (ConP conPtn (ptns))) ids = 
                                    if (normaliseName conPtn == normaliseName nmCons) then
                                        [  [(True,ptnToName $ ptns !! i)]  | i <- ids]
                                    else
                                        -- todo: check if it the current type is well defined, if so add it
                                        [[(False,show nm)]]
                                getIndCallParams nmCons (AsP nm (InfixP ptn1 conPtn ptn2)) ids = 
                                    if (normaliseName conPtn == normaliseName nmCons) then
                                        [  [(True,ptnToName $ [ptn1,ptn2] !! i)]  | i <- ids]
                                    else
                                        [[(False, show nm)]]

                                getIndCallParams nmCons (VarP nmv) ids = [[(False, show nmv)]]
                                               
                                ptnToName (VarP nmv) = show nmv
                                ptnToName (v) = show v

recursiveBangsInd cons clss = failWith $ "Unimplemented case in exhaustive induction : " ++ show cons ++ show clss
    

    
getRecursiveConstr :: Name -> [Con] -> Q [[Int]]
getRecursiveConstr nm [] = return []
getRecursiveConstr nm (con@(NormalC nmCons bngs):cs) = do   
                                                        rest <- getRecursiveConstr nm cs
                                                        foundBangs <- (searchInBang nm bngs 0) 
                                                        -- reportWarningToUser $ show $ "found" ++ show (foundBangs)++show con
                                                        return (foundBangs:rest)
getRecursiveConstr nm (con@(InfixC bngt1 nmCons bngt2):cs) = do   
                                                        rest <- getRecursiveConstr nm cs
                                                        foundBangs <- (searchInBang nm [bngt1,bngt2] 0) 
                                                        -- reportWarningToUser $ show $ "found" ++ show (foundBangs)++show con
                                                        -- reportWarningToUser $ show $ "found" ++ show (foundBangs:rest)
                                                        return (foundBangs:rest)
getRecursiveConstr nm (con:cs) = do
                                failWith $ "Unimplemented: Cannot get recursive parts of given type " ++ show nm 
                   

-- says which bangs of a single data constructor are recursive
searchInBang :: Name -> [BangType]  -> Int -> Q ([Int])
searchInBang nm [] idx = return []
searchInBang nm ((b,(AppT t1 t2)):bs) idx = do
                                                rest <- searchInBang nm bs (idx+1)
                                                b1 <- searchInBang nm [(b,t1)] idx
                                                b2 <- searchInBang nm [(b,t2)] idx
                                                -- res <- do bngT1 <|> bngT2
                                                -- reportWarningToUser $ (show b1 ++ show b2)
                                                
                                                return $ (b1++b2++rest)
searchInBang nm ((b,(ConT nc)):bs) idx = do
                                    rest <- searchInBang nm bs (idx+1)
                                    let isCurrentRec = normaliseName nc == normaliseName nm
                                    -- reportWarningToUser $ (show $  isCurrentRec)
                                    
                                    return $ (if isCurrentRec then [idx] else [])++rest
searchInBang nm ((b,ListT):bs) idx =  do
                                    rest <- searchInBang nm bs (idx+1)
                                    let isCurrentRec = "[]" == (show $ normaliseName nm)
                                    
                                    return $ (if isCurrentRec then [idx] else [])++rest
    -- failWith $ show nm ++ show ListT

    
searchInBang nm (v:bs)  idx = searchInBang nm bs (idx+1)
-- searchInBang nm b@(v:bs)  idx = do
--     rest <- searchInBang nm bs idx
--     reportWarningToUser $ "searchInBang unimplemented given bang: "++show nm++show b++show rest++show bs
--     return []


-- ======================================================
-- |Generates pattern matching given data constructors 
-- and a single declaration clause
-- ======================================================
patternMatchClauses :: Int -> [[Con]] -> Clause -> Q [Clause]
patternMatchClauses 0 _ cls                     = return [cls]
patternMatchClauses n [] (cls)                  = return [cls]
patternMatchClauses n cons cls@(Clause [] b ds) = return [cls]
patternMatchClauses n (cons:cs) (Clause ((VarP nm):vs) b ds) = 
  do
    fpReplaced <- replacePattern cons
    -- given a cls add a parameter to its patterns
    let addParam  p (Clause ptns b ds) = Clause (p:ptns) b ds
    -- "multiplying" single clause to the other pattern matches
    let multiply ((Clause (p:vs) b ds):clss) rest = (map (addParam p) rest) ++ multiply clss rest
        multiply [] rest = []
    restClss <- patternMatchClauses (n-1) cs (Clause (vs) b ds)
    return $ multiply fpReplaced restClss
    where
        typesToIgnore = ["GHC.Types.I#"] -- don't pattern match on these ones (Int) - unused for now

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
                                wildVar <- wildP
                                rest <- generateVars bs
                                -- {- $ mkName $ show -}
                                return $ (VarP  $ mkName $ nameToSmallStr varName):rest 
                                -- return $ wildVar:rest 
        unimplemented = (Clause ((VarP nm):vs) b ds)

patternMatchClauses n _ cls = failWith $ "Unimplemented case for pattern matching generation: " ++ pprint cls




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


                    -- RUNNING through CLI
                    (_, output, _) <- readProcessWithExitCode "liquid" 
                                    liquidArgs ""
                    -- let output = "asd"
                    -- -- RUNNING through Language.Haskell.Liquid.Liquid 
                    -- catch (liquid liquidArgs) (\e -> putStrLn (show (e::SomeException)))
                    

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
generateFromOptions pn pd (Language.Haskell.Liquid.ProofGenerator.Inline:os) = boilerplate pn pd os ("inline " ++ pn)

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
addParamsToType (ForallT tvb ctx tp) extps =  addParamsToTypeStr (pprint tp) extps
addParamsToType (tp) extps =  addParamsToTypeStr (pprint tp) extps

addParamsToTypeStr :: String -> [Name] -> Q (String, [Name])
addParamsToTypeStr [] _ = return ("",[])
addParamsToTypeStr tp [] = do  let (p,ps) = strSplit "->" tp
                               nName <- newName "p"
                               (restWP,addedNames) <- addParamsToTypeStr ps []
                               let finalParts = (nameToSmallStr nName ++ ':':p) : filter (not . strNull) [restWP]
                               return (strJoin "->" finalParts,nName:addedNames)

addParamsToTypeStr tp (ep:eps) = do let (pt,pts) = strSplit "->" tp
                                    (restWP,addedNames) <- addParamsToTypeStr pts eps
                                    let finalParts = (show ep ++ ':':pt) : filter (not . strNull) [restWP]
                                    return (strJoin "->" finalParts,ep:addedNames)



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



multiplyHead :: [[a]] -> [[a]] -> [[a]]
multiplyHead vs [] = vs
multiplyHead [] ys = []
multiplyHead (p:ps) yss =  [ p ++ xs | xs <- yss] ++ multiplyHead ps yss

-- ======================================================
-- |Strip long names (good for debugging)
-- ======================================================
nameToSmallStr :: Name -> String
nameToSmallStr nm = let str = show nm
                    in head str: drop (length str-3) str

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