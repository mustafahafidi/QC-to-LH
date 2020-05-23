{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE  TemplateHaskell #-}
module TH.Main where
    
import TH.Printf
import LiquidHaskell

[lq| nats :: [{ v:Int | 0 <= v }] |]
nats = [0,1,2,3,4,5,6,7,8,9,10]


$(genDecls)



main = do
        putStrLn ( $(pr "Hello") )
        putStrLn . show $ foo 2
    

-- >>> main
-- %s
--
