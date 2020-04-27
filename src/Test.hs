module Test where
import Language.Haskell.Liquid.Prelude
import Lib.CL.CircularList

{-@ LIQUID "--reflection"    @-}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--higherorder"     @-}
{-@ infix   : @-}

-- {-@ prop1:: {b:Bool | x:[] == [x]} @-}
prop1 :: Bool
prop1 = let p1 = (CList [] 0 [1] == CList [1] 0 []) -- not ok
            p2  = (CList [] 0 [] == CList [] 0 []) -- ok 
        in (liquidAssertB p2)
        

main :: IO ()
main = do
            putStrLn $ "prop1: " ++ show prop1 
            putStrLn $ "Test: " ++ show (
                        let  x= CList [] 1 []
                             y= CList [] 0 []
                        in any ((toList x ==). toList) (toList (allRotations y)))
                                         