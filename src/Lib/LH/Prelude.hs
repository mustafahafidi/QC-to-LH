module Lib.LH.Prelude where

import Prelude hiding (length, (++), reverse)

{-@ LIQUID "--no-termination-check" @-}
{-@ measure length @-}
length :: [a] -> Int
length [] = 1
length (_:xs) = 1 + length xs

{-@ infix   ++ @-}
{-@ reflect ++ @-}
(++) :: [a] -> [a] -> [a]
[]       ++ ys = ys
(x : xs) ++ ys = x : (xs ++ ys)



{-@ reflect reverse @-}
reverse :: [a] -> [a]
reverse []     = []
reverse (x:xs) = reverse xs ++ [x]


-- | 'cycle' ties a finite list into a circular one, or equivalently,
-- the infinite repetition of the original list.  It is the identity
-- on infinite lists.

cycle                   :: [a] -> [a]
-- cycle []                = errorEmptyList "cycle"
cycle xs                = xs' where xs' = xs ++ xs'