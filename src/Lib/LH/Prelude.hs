module Lib.LH.Prelude where
import Language.Haskell.Liquid.ProofCombinators

import Prelude hiding (length, 
                        (++), 
                        reverse, 
                        iterate, 
                        null, 
                        splitAt,
                        any,
                        id,
                        minimum
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
                              -- [a]@-}
sort            :: (Ord a) => [a] -> [a]
sort []         = []
sort (x:xs)     = insertSort x (sort xs) 

{-@ reflect insertSort @-}
{-@ insertSort :: Ord t => t -> OList t -> OList t @-} 
                                -- [t]->[t]
                                --OList t -> OList t
insertSort :: Ord t => t -> [t] -> [t]
insertSort y []                   = [y]
insertSort y (x : xs) | y <= x    = y : x : xs 
                  | otherwise = x : insertSort y xs


{-@ reflect minimum  @-}
-- {-@ minimum :: Ord a => {ls:[a] | len ls >0} -> a @-}
minimum :: Ord a => [a] -> a
minimum (x:y:xs) 
 |x > y = minimum (y:xs)
 |x <= y = minimum (x:xs)
minimum (x:_) = x

{-@ reflect \\  @-}
infix \\
(\\) :: Eq a => [a] -> [a] -> [a]
ls \\ rs = ls --TODO


{-======================================================
               Needed only to Lift Eq CList
=======================================================-}

{-@ reflect any @-}
any :: (a -> Bool) -> [a] -> Bool
any _ []        = False
any p (x:xs)    = p x || any p xs


data LMaybe a = LNothing | LJust a
                deriving (Show, Eq)

{-@ data LMaybe a = LNothing | LJust a
 @-}
 
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

{-@ reflect joinTuple @-}
joinTuple ::  e -> (e,e)
joinTuple a     = (a,a)
 
{-@ reflect comp @-}
infixr 9 `comp`
comp :: (b -> c) -> (a -> b) -> a -> c   
f `comp` g = \x -> f(g(x))


{-======================================================
            SOME PRELUDE Theorems
=======================================================-}

singletonP :: a -> Proof
{-@ singletonP :: x:a -> { reverse [x] == [x] } @-}
singletonP x
  =   reverse [x]
  === reverse [] ++ [x]
  === [] ++ [x]
  === [x]
  *** QED 

{-@ rewrite involutionP @-}
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

{-@ rewrite distributivityP @-}
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
    
{-@ rewrite rightIdP @-}
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

{-@ rewrite assocP @-}
{-@ ple assocP @-}
{-@ assocP :: xs:[a] -> ys:[a] -> zs:[a] 
          -> { xs ++ (ys ++ zs) == (xs ++ ys) ++ zs }  @-}
assocP :: [a] -> [a] -> [a] -> Proof
assocP [] _ _       = trivial
assocP (x:xs) ys zs = assocP xs ys zs


{-@ rewrite splitAt_theorem @-}
{-@ inline splitAt_theorem_p @-}
{-@ splitAt_theorem_p ::   n:Int -> a:{[t]| length a >= n} -> Bool @-}
splitAt_theorem_p n as =  let (l,r) = splitAt n as
                          in (l ++ r == as)
{-@ splitAt_theorem ::   n:Int -> a:{[t]| length a >= n} -> { splitAt_theorem_p n a } @-}
splitAt_theorem ::  Eq a => Int -> [a] ->  Proof
splitAt_theorem 0 as = let (l,r) = splitAt 0 as
                                === ([], as)
                        in ((l ++ r) == as)
                        ===([] ++ as == as)
                        ===(as == as)
                    ***QED

splitAt_theorem n ls@(a:as) = let (b1, b2) = splitAt (n - 1) as
                                  (l,r) = splitAt n ls
                                        === (a:b1, b2)
                              in (l ++ r == ls)
                            ===  ((a:b1) ++ b2 == ls)
                            ===  (a:(b1 ++ b2) == ls)
                                ? splitAt_theorem (n-1) as
                                ? (b1++b2 == as)
                            ===  (a:as == ls)
                    ***QED

------- sort theorems
{-@ inline  th_sort_arg_rev_p @-}
th_sort_arg_rev_p ls rs = sort (ls++rs) == sort (rs++ls)

{-@ th_sort_arg_rev :: Ord a =>  ls:[a] -> rs:[a] -> {  th_sort_arg_rev_p ls rs } @-}
th_sort_arg_rev ls rs =  sort (ls++rs)  ==! sort (rs++ls)
                            ***Admit
-------------
{-@ inline  th_sort_arg_app_p @-}
th_sort_arg_app_p ls rs = sort (ls++rs) == sort (sort ls++rs)

{-@ th_sort_arg_app :: Ord a =>  ls:[a] -> rs:[a] -> {  th_sort_arg_app_p ls rs } @-}
th_sort_arg_app ls rs =  sort (ls++rs)  ==! sort (sort ls++rs)
                            ***Admit
-------------
{-@ inline  th_sort_arg_cons_p @-}
th_sort_arg_cons_p l rs = sort (l:rs) == sort (l:sort rs)

{-@ th_sort_arg_cons :: Ord a =>  l:a -> rs:[a] -> {  th_sort_arg_cons_p l rs } @-}
th_sort_arg_cons l rs =  sort (l:rs) == sort (l:sort rs)
                            ***Admit
-------------

{-@ rewrite append_length @-}
{-@ append_length ::  ls:[a] -> rs:[a] -> { length (ls ++ rs) == length ls + length rs} @-}
append_length ::  [a] -> [a] -> Proof
append_length ls rs = length (ls ++ rs) == length ls + length rs
                    ***QED
