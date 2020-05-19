{-# LANGUAGE  TemplateHaskell #-}
module TH.Main where
    
import TH.Printf ( pr )



main = putStrLn ( $(pr "Hello") )


-- >>> main
-- %s
--
