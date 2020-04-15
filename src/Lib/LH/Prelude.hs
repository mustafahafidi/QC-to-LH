module Lib.LH.Prelude where

import Prelude hiding (length, (++), reverse, iterate, null)
import Lib.LH.Equational

{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--no-termination-check" @-}
{-@ LIQUID "--reflection"    @-}

{-@ measure length @-}
{-@ length :: x:[a] -> { length x >=0 } @-}
length :: [a] -> Int
length [] = 0
length (_:xs) = 1 + length xs

{-@ reflect null @-}
{-@ null :: l:[a] -> {v:Bool | not v <=> len l > 0} @-}
null :: [a] -> Bool
null [] = True
null xs = False 

    
{-@ infix   ++ @-}
{-@ reflect ++ @-}
{-@ (++) :: xs:[a] -> ls:[a] -> {vs:[a] | length vs == (length xs) + (length ls) } @-}
(++) :: [a] -> [a] -> [a]
[]       ++ ys = ys
(x : xs) ++ ys = x : (xs ++ ys)


{-@ reflect reverse @-}
{-@ reverse :: xs:[a] -> {ls:[a] | length ls == length xs} @-}
reverse :: [a] -> [a]
reverse []     = []
reverse (x:xs) = reverse xs ++ [x]


-- | 'cycle' ties a finite list into a circular one, or equivalently,
-- the infinite repetition of the original list.  It is the identity
-- on infinite lists.

cycle                   :: [a] -> [a]
-- cycle []                = errorEmptyList "cycle"
cycle xs                = xs' where xs' = xs ++ xs'


{-@ lazy iterate @-}
{-@ iterate :: (a -> a) -> a -> [a] @-}
iterate :: (a -> a) -> a -> [a]
iterate f x =  x : iterate f (f x)

{-@ (==>) :: p:Bool -> q:Bool -> {v:Bool | v <=> (p ==> q)} @-}
False ==> False = True
False ==> True  = True
True  ==> True  = True
True  ==> False = False