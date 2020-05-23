{-# LANGUAGE  TemplateHaskell #-}

module TH.Test where
import TH.Main
import TH.TestProps


import Language.Haskell.TH


-- $(generateProof [|ttt|])
main :: IO ()
main = putStrLn $(do
        Just nm <- lookupValueName "ttt"
        info <- reify nm
        stringE . show $ info)

-- $(parsePropName "ttt")

-- >>> main
-- VarI TH.Test_Proofs.ttt (ConT GHC.Types.Int) Nothing
--
