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

prop_list :: CList Int -> Bool
prop_list c = c == (fromList . toList $ c)

prop_rot :: CList Int -> Bool
prop_rot c = c == (rotR $ rotL c)

-- Make sure converting to/from lists works.

prop_packL :: CList Int -> Bool
prop_packL c = c == (packL c)

prop_packR :: CList Int -> Bool
prop_packR c = c == (packR c)

-- Additional properties

prop_singleton :: Int -> Bool
prop_singleton i = toList (singleton i) == [i]

prop_update :: Int -> CList Int -> Bool
prop_update v cl@Empty = size (update v cl) == 1
prop_update v cl = size (update v cl) == size cl



prop_focus_update :: Int -> CList Int -> Bool
prop_focus_update v cl = focus(update v cl) == Just v


prop_reverse_direction ::  CList Int -> Bool
prop_reverse_direction cl = reverseDirection (reverseDirection cl) == cl && size (reverseDirection cl) == size cl



prop_insertR :: Int -> CList Int -> Bool
prop_insertR i cl = let r = (insertR i cl) in
                        size r == size cl+1

prop_removeR :: CList Int -> Bool
prop_removeR cl@Empty = size (removeR cl) == 0
prop_removeR cl = size (removeR cl) == (size cl)-1

prop_insertR_removeR :: Int -> CList Int -> Bool
prop_insertR_removeR v cl = removeR (insertR v cl) == cl

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

    -- Additional
    putStrLn "prop_singleton"
    quickCheck prop_singleton

    putStrLn "prop_update"
    quickCheck prop_update

    putStrLn "prop_focus_update"
    quickCheck prop_focus_update

    putStrLn "prop_reverse_direction"
    quickCheck prop_reverse_direction

    putStrLn "prop_insertR"
    quickCheck prop_insertR


    putStrLn "prop_removeR"
    quickCheck prop_removeR

    putStrLn "prop_insertR_removeR"
    quickCheck prop_insertR_removeR