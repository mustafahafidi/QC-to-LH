module Main where
import Lib.LH.Prelude
-- import Lib.LH.Equational
import Lib.CL.CircularList
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (length, null, splitAt, (++), reverse)

{-@ LIQUID "--reflection"    @-}
{-@ LIQUID "--no-totality"    @-}

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



{- ===============  Additional ====================-}

{-@ prop_singleton :: i:Int -> {toList (singleton i) == [i]} @-}
prop_singleton :: Int -> Proof
prop_singleton i = toList (singleton i) === [i]
                    ***QED 



{-@ prop_focus_update :: v:Int -> cl:CList Int -> 
                        { focus (update v cl) == Just v} 
@-}
prop_focus_update :: Int -> CList Int -> Proof
prop_focus_update v cl = focus (update v cl) === Just v
                          ***QED 



{-@ prop_reverse_direction ::  cl:CList Int -> 
                { reverseDirection (reverseDirection cl) == cl && 
                  size (reverseDirection cl) == size cl} @-}
prop_reverse_direction ::  CList Int -> Proof
prop_reverse_direction cl = (reverseDirection (reverseDirection cl) === cl
                            ***QED)
                            &&& (size (reverseDirection cl) === size cl
                            ***QED)
                          

{-@ prop_insertR ::  i:Int -> cl:CList Int -> {size (insertR i cl) == size cl+1} @-}
prop_insertR ::  Int -> CList Int -> Proof
prop_insertR i cl = size (insertR i cl) === size cl+1
                          ***QED 


{-@ prop_insertR_removeR ::  v:Int -> cl:CList Int -> {removeR (insertR v cl) == cl} @-}
prop_insertR_removeR ::  Int -> CList Int -> Proof
prop_insertR_removeR v cl = removeR (insertR v cl)
                         === (case cl of
                                Empty -> removeR (CList [] v [])
                                (CList l f r) -> removeR (CList l v (f:r)))
                            
                            === cl
                            ***QED



{-@ prop_update :: v:Int -> cl:CList Int -> 
                 { cl == Empty ==> size (update v cl) == 1 && 
                   cl != Empty ==> size (update v cl) == size cl } 
@-}
prop_update :: Int -> CList Int -> Proof
prop_update v cl@Empty = size (update v cl) 
                        === size (CList [] v [])
                        === 1
                         ***QED 
                         
prop_update v cl@(CList l _ r) = size (update v cl) 
                    === size (CList l v r) 
                    === size cl
                    ***QED 

{-@ prop_removeR ::  cl:CList Int -> 
                { cl == Empty ==> size (removeR cl) == 0 &&
                  cl != Empty ==> size (removeR cl) == (size cl)-1 } @-}
prop_removeR ::  CList Int -> Proof
prop_removeR cl@Empty = size (removeR cl) === 0
                    ***QED 
prop_removeR cl@(CList [] _ []) =   size (removeR cl) ===
                                    size (Empty)      ===
                                    (size cl)-1
                                 ***QED
prop_removeR cl@(CList l _ (r:rs)) =  size (removeR cl) ===
                                      size (CList l r rs)      ===
                                      (size cl)-1
                                 ***QED
prop_removeR  cl@(CList l _ []) = size (removeR cl) ===
                               (let (f:rs)=reverse l in
                                size(CList [] f rs))  ===
                               (size cl)-1
                                ***QED


main :: IO ()
main = putStrLn (show $ toList (reverseDirection (fromList [1,2,3,4])))

