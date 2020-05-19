-- import Lib.QC.Heap (merge, Heap(..))
import Prelude hiding (minimum)
import Language.Haskell.Liquid.ProofCombinators hiding ((==.))
import Test_Heap
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}

-- {-@ reflect minimum  @-}
-- {-@ minimum :: Ord a => {ls:[a] | len ls >0} -> a @-}
-- minimum :: Ord a => [a] -> a
-- minimum (x:y:xs) 
--  |x > y = minimum (y:xs)
--  |x <= y = minimum (x:xs)
-- minimum (x:_) = x

{-@ (==.) :: x:a -> y:{a | x == y} -> a @-}
(==.) :: a -> a -> a 
_ ==. x = x 
{-# INLINE (==.) #-} 


test :: Proof
test = 1 
    ==.1
    ==.1
     ***QED