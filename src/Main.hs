module Main where
import Lib.LH.Prelude
-- import Lib.LH.Equational
import Lib.CL.CircularList
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (length, null, splitAt, (++))

{-@ LIQUID "--reflection"    @-}

-- {-@ LIQUID "--prune-unsorted"    @-}



{-@ prop_empty :: { length (toList empty) == 0} @-}
prop_empty :: Proof
prop_empty = length (toList empty) === 0
             ***QED 


{-@ prop_isEmpty :: l:[Int] -> { null l == isEmpty (fromList l)} @-}
prop_isEmpty :: [Int] -> Proof
prop_isEmpty l = null l === isEmpty (fromList l)
             ***QED 



{-@ prop_size :: l:[Int] -> { (length l) == (size (fromList l)) } @-}
prop_size :: [Int] -> Proof
prop_size l = (length l) === (size (fromList l))
             ***QED 
             
             
{-@ prop_focus :: c:CList Int -> v:Int -> {(Just v) == (focus (insertR v c))} @-}
prop_focus :: CList Int -> Int -> Proof
prop_focus c v = (Just v) === (focus $ insertR v c)
                  ***QED 
                  

-- Proved by assuming the safety of ref. type of reflected functions
{-@ prop_list :: c:CList Int -> {c == (fromList (toList  c))} @-}
prop_list :: CList Int -> Proof
prop_list c = c === (fromList (toList c))
                  ***QED 
                  
 
{-@  prop_rot :: c:CList Int -> {c == (rotR (rotL c))} @-}
prop_rot :: CList Int -> Proof
prop_rot c = c === (rotR (rotL c))
                ***QED 

{- Additional -}

{-@ prop_singleton :: i:Int -> {toList (singleton i) == [i]} @-}
prop_singleton :: Int -> Proof
prop_singleton i = toList (singleton i) === [i]
                    ***QED 


{- How to prove with pattern matching? -}
{-@ prop_update :: i:Int -> cl:CList Int -> Proof @-}
prop_update :: Int -> CList Int -> Proof
prop_update v cl@Empty = trivial
prop_update v cl = trivial



{-@ prop_focus_update :: v:Int -> cl:CList Int -> { focus (update v cl) == Just v} @-}
prop_focus_update :: Int -> CList Int -> Proof
prop_focus_update v cl = focus (update v cl) === Just v
                          ***QED 

{-@ prop_reverse_direction ::  cl:CList Int -> {reverseDirection (reverseDirection cl) == cl && size (reverseDirection cl) == size cl} @-}
prop_reverse_direction ::  CList Int -> Proof
prop_reverse_direction cl = (reverseDirection (reverseDirection cl) === cl
                            ***QED)
                            &&& (size (reverseDirection cl) === size cl
                            ***QED)
                          





main :: IO ()
main = putStrLn (show $ "Hello world")

