{-# OPTIONS -Wall #-}
module Lib.CL.QuickCheck where

import Test.QuickCheck
import Lib.CL.CircularList
-- import Lib.LH.Prelude hiding (length)


-- Make sure empty really is empty.
prop_empty :: Bool
prop_empty = length (toList empty) == 0

prop_isEmpty :: [Int] -> Bool
prop_isEmpty l = null l == isEmpty (fromList l)

prop_size :: [Int] -> Bool
prop_size l = (length l) == (size . fromList $ l)

prop_focus :: CList Int -> Int -> Bool
prop_focus c v = (Just v) == (focus $ insertR v c)

-- Make sure converting to/from lists works.
prop_list :: CList Int -> Bool
prop_list c = c == (fromList . toList $ c)


prop_rot :: CList Int -> Bool
prop_rot c = c == (rotR $ rotL c)

prop_packL :: CList Int -> Bool
prop_packL c = c == (packL c)

prop_packR :: CList Int -> Bool
prop_packR c = c == (packR c)


main :: IO ()
main = do
    putStrLn "prop_empty"
    quickCheck prop_empty

    putStrLn "prop_list"
    quickCheck prop_list
    
    putStrLn "prop_rot"
    quickCheck prop_rot

    putStrLn "prop_focus"
    quickCheck prop_focus

    putStrLn "prop_packL"
    quickCheck prop_packL

    putStrLn "prop_packR"
    quickCheck prop_packR

    putStrLn "prop_isEmpty"
    quickCheck prop_isEmpty

    putStrLn "prop_size"
    quickCheck prop_size
