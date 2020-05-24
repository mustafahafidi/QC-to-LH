{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE  TemplateHaskell #-}
module TH.Main where
    
-- import Lib.LH.Prelude ((++))
-- import Prelude hiding ((++))
import Language.Haskell.TH
import LiquidHaskell
import Language.Haskell.Liquid.ProofCombinators

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
generateProof exp =  [d| [lq| prop_proof :: {v:()| exp } |]
                         prop_proof = toProof $(exp) |]