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



{-@ prop_size :: l:[Int] -> { (length l) == (size (fromList l)) } @-}
prop_size :: [Int] -> Proof
prop_size l = (length l) ==. (size (fromList l))
             ***QED 
             
             
{-@ prop_focus :: c:CList Int -> v:Int -> {(Just v) == (focus (insertR v c))} @-}
prop_focus :: CList Int -> Int -> Proof
prop_focus c v = (Just v) ==. (focus $ insertR v c)
                  ***QED 
                  

-- Proved by assuming the safety of ref. type of reflected functions
{-@ prop_list :: c:CList Int -> {c == (fromList (toList  c))} @-}
prop_list :: CList Int -> Proof
prop_list c = c ==. (fromList (toList c))
                  ***QED 
                  
 
{-@  prop_rot :: c:CList Int -> {c == (rotR (rotL c))} @-}
prop_rot :: CList Int -> Proof
prop_rot c = c ==. (rotR (rotL c))
                ***QED 

{- 
reverseCList :: CList a -> CList a
reverseCList Empty = Empty
reverseCList (CList ls f rs) = CList 
 -}

main :: IO ()
main = putStrLn (show $ "Hello world")

