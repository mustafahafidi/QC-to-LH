module Lib.LH.Prelude where
import Language.Haskell.Liquid.ProofCombinators

import Prelude hiding (length, 
                        (++), 
                        reverse, 
                        iterate, 
                        null, 
                        splitAt,
                        any,
                        id
                        )

{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--no-termination-check" @-}
{-@ LIQUID "--reflection"    @-}
{-@ LIQUID "--ple-local"    @-}
 
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

    
{-@ infix 4  ++ @-}
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


{-@ reflect splitAt @-}
{-@ splitAt :: n:Int
            -> a:{[t]| length a >= n}
            -> {b:([t], [t])| length (snd b) = length a - n && n = length (fst b)} @-}
splitAt :: Int -> [a] -> ([a], [a])
splitAt 0         as  = ([], as)
splitAt n (a:as) = let (b1, b2) = splitAt (n - 1) as
                        in (a:b1, b2)


{-@ type OList a    = [a]<{\fld v -> (v >= fld)}> @-}

{-@ reflect sort @-}
{-@ sort :: (Ord a) => xs:[a] -> OList a @-}
sort            :: (Ord a) => [a] -> [a]
sort []         = []
sort (x:xs)     = insertSort x (sort xs) 

{-@ reflect insertSort @-}
{-@ insertSort :: Ord t => t -> OList t -> OList t @-}
insertSort :: Ord t => t -> [t] -> [t]
insertSort y []                   = [y]
insertSort y (x : xs) | y <= x    = y : x : xs 
                  | otherwise = x : insertSort y xs


{-======================================================
                Trying to lift Eq CList
=======================================================-}

{-@ reflect any @-}
any :: (a -> Bool) -> [a] -> Bool
any _ []        = False
any p (x:xs)    = p x || any p xs


data LMaybe a = LNothing | LJust a
                deriving (Show, Eq)

{-@ reflect unfoldr @-}
unfoldr :: (b -> LMaybe (a, b)) -> b -> [a]
unfoldr f b0 = case f b0 of
                LJust (a, new_b) -> a : (unfoldr f new_b)
                LNothing         -> []


{-@ reflect fmapLMaybe @-}
fmapLMaybe :: (a->b) -> LMaybe a -> LMaybe b
fmapLMaybe _ LNothing       = LNothing
fmapLMaybe f (LJust a)      = LJust (f a)

{-@ reflect >>*= @-}
{-@ infix >>*= @-}
-- infix >>*=
f >>*= k = \ r -> k (f r) r

{-@ reflect id @-}
id x = x

{-@ reflect join @-}
join ::  (e -> e -> a) -> e -> a
join x            =  x >>*= id
 


{-    ==================== SOME PRELUDE PROOFS ====================  -}

singletonP :: a -> Proof
{-@ singletonP :: x:a -> { reverse [x] == [x] } @-}
singletonP x
  =   reverse [x]
  === reverse [] ++ [x]
  === [] ++ [x]
  === [x]
  *** QED 

{-@ involutionP :: xs:[a] -> {reverse (reverse xs) == xs } @-}
involutionP :: [a] -> Proof 
involutionP [] 
  =   reverse (reverse []) 
      -- applying inner reverse
  === reverse []
      -- applying reverse
  === [] 
  *** QED 
involutionP (x:xs) 
  =   reverse (reverse (x:xs))
      -- applying inner reverse
  === reverse (reverse xs ++ [x])
      ? distributivityP (reverse xs) [x]
  === reverse [x] ++ reverse (reverse xs) 
      ? involutionP xs 
  === reverse [x] ++ xs 
      ? singletonP x 
  === [x] ++ xs
      -- applying append on []
  === x:([]++ xs)
      -- applying ++
  === (x:xs)
  *** QED 

{-@ distributivityP :: xs:[a] -> ys:[a] -> {reverse (xs ++ ys) == (reverse ys) ++ (reverse xs)} @-}

distributivityP :: [a] -> [a] -> Proof
distributivityP [] ys =   reverse ([] ++ ys)
    === reverse ys 
        ? rightIdP (reverse ys) 
    === reverse ys ++ []
    === reverse ys ++ reverse []
    *** QED 
distributivityP (x:xs) ys  =   reverse ((x:xs) ++ ys)
    === reverse (x:(xs ++ ys))
    === reverse (xs ++ ys) ++ [x]
        ? distributivityP xs ys 
    === (reverse ys ++ reverse xs) ++ [x]
        ? assocP (reverse ys) (reverse xs) [x]
    === reverse ys ++ (reverse xs ++ [x])
    === reverse ys ++ reverse (x:xs)
    *** QED 


{-@ rightIdP :: xs:[a] -> { xs ++ [] == xs } @-}
rightIdP :: [a] -> Proof
rightIdP []     
  =   [] ++ [] 
  === [] 
  *** QED 
rightIdP (x:xs)
  =   (x:xs) ++ [] 
  === x : (xs ++ [])
      ? rightIdP xs
  === x : xs
  *** QED

{-@ ple assocP @-}
{-@ assocP :: xs:[a] -> ys:[a] -> zs:[a] 
          -> { xs ++ (ys ++ zs) == (xs ++ ys) ++ zs }  @-}
assocP :: [a] -> [a] -> [a] -> Proof
assocP [] _ _       = trivial
assocP (x:xs) ys zs = assocP xs ys zs