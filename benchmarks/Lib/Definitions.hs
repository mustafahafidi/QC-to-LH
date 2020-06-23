module Lib.Definitions where

import Prelude hiding (take, drop,
                      (++),
                      (+),(-), (<=), (<), min, max, length,elem,not,dropWhile,takeWhile, last,zip,
                      null
                      )
                      
import qualified Prelude as P

data NAT = Z | S NAT
  deriving (Eq,Show,Ord)

data Tree a = Leaf | Node (Tree a) a (Tree a)
  deriving (Eq,Ord,Show)

{-@ LIQUID "--exactdc" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

{-@ reflect natToInt @-}
{-@ natToInt :: NAT -> {n:Int | n>=0 } @-}
natToInt :: NAT -> Int
natToInt Z = 0
natToInt (S n) = 1 P.+ natToInt n
  

{-@ infix 4  ++ @-}
{-@ reflect ++ @-}
-- {-@ (++) :: xs:[a] -> ls:[a] -> {vs:[a] | len vs == (len xs) + (len ls) } @-}
(++) :: [a] -> [a] -> [a]
[]       ++ ys = ys
(x : xs) ++ ys = x : (xs ++ ys)

{-@ reflect drop @-}
drop :: NAT -> [a] -> [a]
drop Z xs = xs
drop _ [] = []
drop (S x) (_:xs) = drop x xs

{-@ reflect take @-}
take :: NAT -> [a] -> [a]
take Z _ = []
take _ [] = []
take (S x) (y:ys) = y : (take x ys)


{-@ reflect count @-}
count :: NAT -> [NAT] -> NAT
count x [] = Z
count x (y:ys) =
  case x == y of
    True -> S (count x ys)
    _ -> count x ys


{-@ reflect not @-}
not :: Bool -> Bool
not True = False
not False = True

{-@ reflect delete @-}
delete :: NAT -> [NAT] -> [NAT]
delete _ [] = []
delete n (x:xs) =
  case n == x of
    True -> delete n xs
    False -> x : (delete n xs)

{-@ reflect takeWhile @-}
takeWhile :: (a -> Bool) -> [a] -> [a]
takeWhile _ [] = []
takeWhile p (x:xs) =
  case p x of
    True -> x : (takeWhile p xs)
    _ -> []

{-@ reflect dropWhile @-}
dropWhile :: (a -> Bool) -> [a] -> [a]
dropWhile _ [] = []
dropWhile p (x:xs) =
  case p x of
    True -> dropWhile p xs
    _ -> x:xs

-- -- infixl 6  +
-- {-@ reflect == @-}
-- Z     == Z     = True
-- Z     == _     = False
-- (S _) == Z     = False
-- (S x) == (S y) = x == y

{-@ reflect min @-}
min Z     y     = Z
min (S x) Z     = Z
min (S x) (S y) = S (min x y)

{-@ reflect max @-}
max Z     y     = y             --
max x     Z     = x
max (S x) (S y) = S (max x y)

infixl 6  +
{-@ reflect + @-}
Z     + y = y
x     + Z = x
(S x) + y = S (x + y)

infixl 6  -
{-@ reflect - @-}
Z     - _     = Z
x     - Z     = x
(S x) - (S y) = x - y

infix  4  <<=
{-@ reflect <<= @-}
-- {-@ (<=) :: n1:NAT -> n2:NAT -> { natToInt n1 <<= natToInt n2 } @-}
Z     <<= _     = True
_     <<= Z     = False
(S x) <<= (S y) = x <<= y

infix  4  <<
{-@ reflect << @-}
_     << Z     = False
Z     << _     = True
(S x) << (S y) = x << y

infix 0 ==>
{-@ reflect ==> @-}
True ==> False = False
False ==> _ = True
_ ==> _ = True

{-@ reflect length @-}
length :: [a] -> NAT
length [] = Z
length (_:xs) = S (length xs)

{-@ reflect null @-}
null :: [a] -> Bool
null [] = True
null _  = False

{-@ reflect butlastConcat @-}
butlastConcat :: [a] -> [a] -> [a]
butlastConcat xs [] = butlast xs
butlastConcat xs ys = xs ++ butlast ys

{-@ reflect butlast @-}
butlast :: [a] -> [a]
butlast [] = []
butlast [x] = []
butlast (x:xs) = x:(butlast xs)

{-@ reflect last @-}
last :: [NAT] -> NAT
last [] = Z
last [x] = x
last (x:xs) = last xs

{-@ reflect sorted @-}
sorted :: [NAT] -> Bool
sorted [] = True
sorted [x] = True
sorted (x:y:ys) = (x <<= y) && sorted (y:ys)

{-@ reflect insort @-}
insort :: NAT -> [NAT] -> [NAT]
insort n [] = [n]
insort n (x:xs) =
  case n <<= x of
    True -> n : x : xs
    _ -> x : (insort n xs)

{-@ reflect insert @-}
insert :: NAT -> [NAT] -> [NAT]
insert n [] = [n]
insert n (x:xs) 
  | n<<x = n : x : xs
  | otherwise = x : (insert n xs)


{-@ reflect ins1 @-}
ins1 :: NAT -> [NAT] -> [NAT]
ins1 n [] = [n]
ins1 n (x:xs) =
  case n == x of
    True -> x : xs
    _ -> x : (ins1 n xs)

{-@ reflect sort @-}
sort :: [NAT] -> [NAT]
sort [] = []
sort (x:xs) = insort x (sort xs)

{-@ reflect elem @-}
elem :: NAT -> [NAT] -> Bool
elem _ [] = False
elem n (x:xs) =
  case n == x of
    True -> True
    False -> elem n xs


{-@ reflect rev @-}
rev :: [a] -> [a]
rev [] = []
rev (x:xs) = rev xs ++ [x]


{-@ reflect lastOfTwo @-}
lastOfTwo :: [NAT] -> [NAT] -> NAT
lastOfTwo xs [] = last xs
lastOfTwo _ ys = last ys

{-@ reflect zip @-}
zip :: [a] -> [b] -> [(a, b)]
zip [] _ = []
zip _ [] = []
zip (x:xs) (y:ys) = (x, y) : (zip xs ys)

{-@ reflect zipConcat @-}
zipConcat :: a -> [a] -> [b] -> [(a, b)]
zipConcat _ _ [] = []
zipConcat x xs (y:ys) = (x, y) : zip xs ys


{-@ reflect height @-}
height :: Tree a -> NAT
height Leaf = Z
height (Node l x r) = S (max (height l) (height r))

{-@ reflect mirror @-}
mirror :: Tree a -> Tree a
mirror Leaf = Leaf
mirror (Node l x r) = Node (mirror r) x (mirror l)


{-@ reflect const @-}
const :: a -> b -> a
const v _ = v



{-@ reflect double @-}
double :: NAT -> NAT
double Z     = Z
double (S x) = S (S (double x))


{-@ reflect qrev @-}
qrev :: [a] -> [a] -> [a]
qrev []     acc = acc
qrev (x:xs) acc = qrev xs (x:acc)