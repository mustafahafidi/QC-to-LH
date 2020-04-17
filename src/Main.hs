module Main where
import Lib.LH.Prelude
import Lib.LH.Equational
import Lib.CL.CircularList
import Prelude hiding (length, null, splitAt, (++))

{-@ LIQUID "--reflection"    @-}

-- {-@ LIQUID "--prune-unsorted"    @-}



{-@ prop_empty :: { length (toList empty) == 0} @-}
prop_empty :: Proof
prop_empty = length (toList empty) ==. 0
             ***QED 


{-@ prop_isEmpty :: l:[Int] -> { null l == isEmpty (fromList l)} @-}
prop_isEmpty :: [Int] -> Proof
prop_isEmpty l = null l ==. isEmpty (fromList l)
             ***QED 




main :: IO ()
main = putStrLn (show $ "Hello world" ++ show (splitAt 2 [1,2,3,4]))

