 
module AddCommuteZeno where
import Prelude ()
import Zeno
data NAT = Z | S NAT
data Tree a = Leaf | Node (Tree a) a (Tree a)
{-======================================================
                        prop_01 (PROVED)
=======================================================-}
prop_01 n xs = prove (take n xs ++ drop n xs :=: xs)
{-======================================================
                        prop_02 (PROVED)
=======================================================-}
prop_02  n xs ys = prove (count n xs + count n ys :=: count n (xs ++ ys))
{-======================================================
                   prop_03 (PROVED)
=======================================================-}
prop_03 n xs ys = proveBool ((count n xs <<= count n (xs ++ ys)))
   
{-======================================================
                  prop_04 (PROVED)
=======================================================-}
prop_04 n xs
  = prove (S (count n xs) :=: count n (n : xs))
{-======================================================
                        prop_05 (NOT-PROVED)
=======================================================-}
prop_05 n x xs
  = proveBool ((n == x) ==> (S (count n xs) == count n (x : xs)))
{-======================================================
                        prop_06
=======================================================-}
prop_06 n m = proveBool ((n - (n + m)) == Z)
{-======================================================
                        prop_07
=======================================================-}
prop_07 n m = proveBool(((n + m) - n) == m)
{-======================================================
                        prop_08
=======================================================-}
prop_08 k m n = proveBool(((k + m) - (k + n)) == (m - n))
{-======================================================
                        prop_09
=======================================================-}
prop_09 i j k
  = proveBool(((i - j) - k) == (i - (j + k)))
{-======================================================
                        prop_10
=======================================================-}
prop_10  m
  = proveBool((m - m) == Z)
{-======================================================
                        prop_11
=======================================================-}
prop_11 xs
  = prove ((drop Z xs) :=: xs)
{-======================================================
                        prop_13
=======================================================-}
prop_13 n x xs
  = prove (drop (S n) (x : xs) :=: drop n xs)
{-======================================================
                   prop_15 (hint: lemma) (cvc4-ok, non-simp-ind)
=======================================================-}
prop_15 n ls = prove (length (insert n ls) :=: S (length ls))
{-======================================================
                 prop_16
=======================================================-}
prop_16 :: NAT -> [NAT] -> Prop
prop_16 x xs = proveBool (((xs == []) ==> (last (x:xs) == x)))
{-======================================================
                   prop_17
=======================================================-}
prop_17 n = proveBool ((n <<= Z) == (n == Z))
{-======================================================
                   prop_18
=======================================================-}
prop_18 i m
  = proveBool (i << S (i + m))
{-======================================================
                        prop_19
=======================================================-}
prop_19 n xs
  = proveBool  (length (drop n xs) == (length xs - n))
{-======================================================
                     prop_20
=======================================================-}
prop_20 xs = proveBool (length (sort xs) == length xs)
{-======================================================
                   prop_21
=======================================================-}
prop_21 n m
  = proveBool (n <<= (n + m))
{-======================================================
                     prop_22
=======================================================-}
prop_22 a b c
  = proveBool (max (max a b) c == max a (max b c))
{-======================================================
                     prop_23
=======================================================-}
prop_23 a b
  = proveBool (max a b == max b a)
{-======================================================
                     prop_24
=======================================================-}
prop_24 a b
  = proveBool (((max a b) == a) == (b <<= a))
{-======================================================
                     prop_25
=======================================================-}
prop_25 a b
  = proveBool (((max a b) == b) == (a <<= b))
{-======================================================
                     prop_26
=======================================================-}
prop_26 x xs ys
  = proveBool ((x `elem` xs) ==> (x `elem` (xs ++ ys)))
{-======================================================
                   prop_27
=======================================================-}
prop_27 x xs ys
  = proveBool ((x `elem` ys) ==> (x `elem` (xs ++ ys)))
{-======================================================
                        prop_28
=======================================================-}
prop_28 x xs
  = proveBool ((x `elem` (xs ++ [x]))) 
{-======================================================
                     prop_29 (hint: induction) (cvc4-ok, non-simp-ind)
=======================================================-}
prop_29 x xs
  = proveBool ((x `elem` ins1 x xs)) 
{-======================================================
                     prop_30 (hint: caseExpand) (non-simp-ind)
=======================================================-}
prop_30 x xs
  = proveBool ((x `elem` (insert x xs))) 
{-======================================================
                        prop_31
=======================================================-}
prop_31 a b c
  = proveBool ((min (min a b) c == min a (min b c))) 
{-======================================================
                        prop_32
=======================================================-}
prop_32 a b
  = proveBool ((min a b == min b a)) 
{-======================================================
                     prop_33
=======================================================-}
prop_33 a b
  = proveBool ((min a b == a) == (a <<= b)) 
{-======================================================
                     prop_34
=======================================================-}
prop_34 a b
  = proveBool ((min a b == b) == (b <<= a)) 


{-======================================================
                     prop_35
=======================================================-}
prop_35 xs
  = proveBool (dropWhile (const False) xs == xs) 
{-======================================================
                     prop_36
=======================================================-}
prop_36 xs
  = proveBool (takeWhile (const True) xs == xs) 
{-======================================================
                     prop_37 (hint: caseExpand) (cvc4-ok, non-simp-ind)
=======================================================-}
prop_37 x xs
  = proveBool (not (x `elem` (delete x xs))) 
{-======================================================
                        prop_38
=======================================================-}
prop_38 n xs
  = proveBool (count n (xs ++ [n]) == S (count n xs)) 
{-======================================================
                        prop_39
=======================================================-}
prop_39 n x xs
  = proveBool ((count n [x] + count n xs) == count n (x:xs)) 
{-======================================================
                        prop_40
=======================================================-}
prop_40 xs
  = proveBool ((take Z xs == [])) 
{-======================================================
                        prop_42
=======================================================-}
prop_42 n x xs
  = proveBool ((take (S n) (x:xs) == x : (take n xs))) 
{-======================================================
                        prop_44
=======================================================-}
prop_44 :: NAT -> [NAT] -> [NAT] -> Prop
prop_44 x xs ys
  = proveBool (((zip (x:xs) ys) `pairEqual1` (zipConcat x xs ys))) 
{-======================================================
                        prop_45
=======================================================-}
prop_45 :: NAT -> NAT -> [NAT] -> [NAT] -> Prop
prop_45 x y xs ys
  = proveBool ((zip (x:xs) (y:ys) `pairEqual1` ((x, y) : zip xs ys))) 
{-======================================================
                        prop_46
=======================================================-}
prop_46 :: [NAT] -> Prop
prop_46 xs
  = proveBool ((zip ([]::[NAT]) xs `pairEqual1` [])) 
{-======================================================
                     prop_47 (hint: lemma)
=======================================================-}
prop_47 a
  = proveBool ((height (mirror a) == height a)) 
{-======================================================
                     prop_48 (hint: caseExpand) (cvc4-ok, non-simp-ind)
=======================================================-}
prop_48 xs
  = proveBool (not (null xs) ==> (butlast xs ++ [last xs] == xs)) 
{-======================================================
                   prop_49 (hint: caseExpand,lemma)
=======================================================-}
prop_49 xs ys
  = proveBool ((butlast (xs ++ ys) == butlastConcat xs ys)) 
{-======================================================
                  prop_50 (hint: caseExpand, induction) (non-simp-ind)
=======================================================-}
prop_50 xs
  = proveBool ((butlast xs == take (length xs - S Z) xs)) 
{-======================================================
                        prop_51
=======================================================-}
prop_51 xs x
  = proveBool ((butlast (xs ++ [x]) == xs)) 
{-======================================================
                   prop_52 (hint: lemma)
=======================================================-}
prop_52 n xs
  = proveBool ((count n xs == count n (rev xs))) 
{-======================================================
                     prop_53 (hint: lemma)
=======================================================-}
prop_53 n xs
  = proveBool ((count n xs == count n (sort xs))) 
{-======================================================
                     prop_54 (hint: lemma)
=======================================================-}
prop_54 n m
  = proveBool (((m + n) - n == m)) 
{-======================================================
                        prop_55
=======================================================-}
prop_55 n xs ys
  = proveBool ((drop n (xs ++ ys) == drop n xs ++ drop (n - length xs) ys)) 
{-======================================================
                     prop_56 (hint: lemma)
=======================================================-}
-- property:
prop_56 n m xs
  = proveBool ((drop n (drop m xs) == drop (n + m) xs)) 
{-======================================================
                        prop_57
=======================================================-}
prop_57 n m xs
  = proveBool ((drop n (take m xs) == take (m - n) (drop n xs))) 
{-======================================================
                        prop_58
=======================================================-}
prop_58 :: NAT -> [NAT] -> [NAT] -> Prop
prop_58 n xs ys
  = proveBool ((drop n (zip xs ys) `pairEqual1` zip (drop n xs) (drop n ys))) 
{-======================================================
                     prop_59 (hint: lemma) (cvc4-ok, non-simp-ind)
=======================================================-}
prop_59 xs ys
  = proveBool ((((ys == []) ==> (last (xs ++ ys) == last xs)))) 
{-======================================================
                       prop_60 (hint:caseExpand,induction) (non-simp-ind)
=======================================================-}
prop_60 xs ys
  = proveBool (not (null ys) ==> (last (xs ++ ys) == last ys)) 
{-======================================================
                     prop_61 (hint: lemma)
=======================================================-}
prop_61 xs ys
  = proveBool ((last (xs ++ ys) == lastOfTwo xs ys)) 
{-======================================================
                     prop_62 (hint: induction) (cvc4-ok, non-simp-ind)
=======================================================-}
prop_62 xs x
  = proveBool (not (null xs) ==> (last (x:xs) == last xs)) 
{-======================================================
                     prop_63 (hint: induction) (non-simp-ind)
=======================================================-}
prop_63 n xs
  = proveBool ((n << length xs) ==> (last (drop n xs) == last xs)) 
{-======================================================
                     prop_64 (hint: induction) (non-simp-ind)
=======================================================-}
  
prop_64 x xs
  = proveBool ((last (xs ++ [x]) == x)) 
{-======================================================
                        prop_65 (hint: lemma)
=======================================================-}
prop_65 i m = proveBool (i << S (m + i)) 
{-======================================================
                     prop_67 (hint: induction) (non-simp-ind)
=======================================================-}
prop_67 xs
  = proveBool ((length (butlast xs) == length xs - S Z)) 
{-======================================================
                     prop_68 (hint: lemma)
=======================================================-}
prop_68 n xs
  = proveBool (length (delete n xs) <<= length xs) 
{-======================================================
                   prop_69  (hint: lemma)
=======================================================-}
prop_69 n m
  = proveBool (n <<= (m + n)) 
{-======================================================
                     prop_70
=======================================================-}
prop_70 m n
  = proveBool (m <<= n ==> (m <<= S n)) 
{-======================================================
                     prop_71 (hint: caseExpand, lemma) (cvc4-ok, non-simp-ind)
=======================================================-}
prop_71 x y xs
  = proveBool (((x == y) == False) ==> (elem x (insert y xs) == elem x xs)) 
{-======================================================
                     prop_72 (hint: lemma)
=======================================================-}
prop_72 i xs
  = proveBool ((rev (drop i xs) == take (length xs - i) (rev xs))) 
{-======================================================
                     prop_75
=======================================================-}
prop_75 n m xs
  = proveBool ((count n xs + count n [m] == count n (m : xs))) 
{-======================================================
                        prop_76
=======================================================-}
prop_76 n m xs
  = proveBool (((n == m) == False) ==> (count n (xs ++ [m]) == count n xs)) 
{-======================================================
                     prop_77 (hint: lemma, caseExpand)
=======================================================-}
prop_77 x xs
  = proveBool (sorted xs ==> sorted (insort x xs)) 
{-======================================================
                   prop_78 (hint: lemma)
=======================================================-}
prop_78 xs
  = proveBool ((sorted (sort xs))) 
{-======================================================
                        prop_79
=======================================================-}
prop_79 m n k
  = proveBool ((((S m - n) - S k) == ((m - n) - k))) 
{-======================================================
                        prop_80
=======================================================-}
prop_80 n xs ys
  = proveBool ((take n (xs ++ ys) == (take n xs ++ take (n - length xs) ys))) 
{-======================================================
                 prop_81 (hint: lemma)
=======================================================-}
prop_81 n m xs 
  = proveBool ((take n (drop m xs) == drop m (take (n + m) xs))) 
{-======================================================
                        prop_82
=======================================================-}
prop_82 :: NAT -> [NAT] -> [NAT] -> Prop
prop_82 n xs ys
  = proveBool ((take n (zip xs ys) `pairEqual1` zip (take n xs) (take n ys))) 
{-======================================================
                        prop_83
=======================================================-}
prop_83 :: [NAT] -> [NAT] -> [NAT] -> Prop
prop_83 xs ys zs
  = proveBool ((zip (xs ++ ys) zs `pairEqual1` (zip xs (take (length xs) zs) ++ zip ys (drop (length xs) zs)))) 
{-======================================================
                        prop_84
=======================================================-}
prop_84 :: [NAT] -> [NAT] -> [NAT] -> Prop
prop_84 xs ys zs
  = proveBool ((zip xs (ys ++ zs) `pairEqual1` (zip (take (length ys) xs) ys ++ zip (drop (length ys) xs) zs))) 
{-======================================================
                   prop_85 (hint: lemma)
=======================================================-}
prop_85 :: [NAT] -> [NAT] -> Prop
prop_85 xs ys
  = proveBool ((length xs == length ys) ==> (zip (rev xs) (rev ys) `pairEqual1` rev (zip xs ys))) 
{-======================================================
                     prop_86 (hint: caseExpand, lemma)
=======================================================-}
prop_86 x y xs
  = proveBool (x << y ==> (elem x (insert y xs) == elem x xs)) 
{-======================================================
                        prop_T01 (hint: lemma)
=======================================================-}
prop_T01 x = proveBool (double x == x + x) 
{-======================================================
                      prop_T02
=======================================================-}
prop_T02 x y = proveBool (length (x ++ y) == length (y ++ x)) 
{-======================================================
                    prop_T03
=======================================================-}
prop_T03 x y = proveBool (length (x ++ y ) == length (y) + length x) 
{-======================================================
                    prop_T04 (hint: lemma)
=======================================================-}
prop_T04 x = proveBool (length (x ++ x) == double (length x)) 
{-======================================================
                    prop_T05 (hint: lemma)
=======================================================-}
prop_T05 x = proveBool (length (rev x) == length x) 
{-======================================================
                    prop_T06 (hint: lemma)
=======================================================-}
prop_T06 x y = proveBool (length (rev (x ++ y )) == length x + length y) 
{-======================================================
                    prop_T07 (hint: lemma)
=======================================================-}
prop_T07 x y = proveBool (length (qrev x y) == length x + length y) 










{-=================================================================
                        DEFINITIONS
===================================================================-}
class Eq a where
  infixr 2 ==
  (==) :: a -> a -> Bool
instance Eq NAT where
    Z     == Z     = True
    Z     == _     = False
    (S _) == Z     = False
    (S x) == (S y) = x == y
    
instance Eq a => Eq [a] where
   [] == [] = True
   (x:xs) == (y:ys) = (x == y) && (xs == ys)
   _ == _ = False
        
instance Eq Bool where
   True == True = True
   False == False = True
   _    == _      = False

instance (Eq a, Eq b) => Eq (a, b) where
    --  Zeno crashes with this instance
    (x,y) == (z,d) = (x == z) && (y == d)


pairEqual1 :: (Eq a, Eq b) => [(a,b)] -> [(a,b)] -> Bool
((x,y):xxs) `pairEqual1` ((z,d):yys) = (x == z) && (y == d) && (xxs `pairEqual1` yys)
_ `pairEqual1` _ = False


pairEqual2 :: (Eq a, Eq b) => (a,b) -> (a,b) -> Bool
(x,y) `pairEqual2` (z,d) = (x == z) && (y == d)


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
infixl 3 && 
True && True = True
_    && _    = False
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