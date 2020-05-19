{-# LANGUAGE  TemplateHaskell #-}

module TH.ProofGenerator where

import Language.Haskell.TH
import Language.Haskell.Liquid.ProofCombinators

gen :: Q Exp -> Q [Dec]
gen prop =  [d| proof = prop ***QED |]
            -- do
            -- pName <- newName "proof"
            -- return [ValD (VarP pName) (NormalB (InfixE (Just (UnboundVarE prop)) (VarE ***) (Just (ConE LQED)))) []]
 

-- >>> runQ [d| proof = prop ***QED  |]
-- [ValD (VarP proof_1) (NormalB (InfixE (Just (UnboundVarE prop)) (VarE Language.Haskell.Liquid.ProofCombinators.***) (Just (ConE Language.Haskell.Liquid.ProofCombinators.QED)))) []]
--
-- [ValD (VarP proof_0) (NormalB (LitE (StringL "Asd"))) []]
--
