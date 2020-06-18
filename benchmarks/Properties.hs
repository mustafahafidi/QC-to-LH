{-# LANGUAGE  QuasiQuotes #-}
{-# LANGUAGE  TemplateHaskell #-}
{-# OPTIONS_GHC -dth-dec-file #-}

{-======================================================
Porting TIP problems from  
https://github.com/tip-org/benchmarks/blob/master/original/isaplanner/Properties.hs

To improve verification time, run this file in LH by pieces (leave uncommented only the proof you want to check)
======================================================-}


import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Liquid.ProofGenerator
import Language.Haskell.Liquid.UX.QuasiQuoter
import Lib.Definitions

import Prelude hiding (take, drop,
                      (++),
                      (+),(-), (<=), (<), min, max,
                      length, elem, not, dropWhile,takeWhile,last,zip
                      )

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--exactdc" @-}
{-@ LIQUID "--ple-local" @-}
{-
{-======================================================
                        prop_01
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpandP:2
prop_01 :: Eq a => NAT  -> [a] -> Bool
prop_01 n xs = (take n xs ++ drop n xs == xs)
|]

{-======================================================
                        prop_02
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpandP:2
prop_02 :: NAT -> [NAT] -> [NAT] -> Bool
prop_02  n xs ys = (count n xs + count n ys == count n (xs ++ ys))
|]


{-======================================================
                   prop_03 (hint-lemma)
=======================================================-}
{-@ rewriteWith prop_03_proof [lemma_count_proof] @-}
[lhp|genProp|reflect|ple
prop_03 :: NAT -> [NAT] -> [NAT] -> Bool
prop_03 n xs ys
  = count n xs <= count n (xs ++ ys)
    -- ? lemma_count_proof n xs ys
    ? lemma_diseq_proof (count n xs) (count n ys)
|]

[lhp|genProp|inline|admit
lemma_count :: NAT -> [NAT] -> [NAT] -> Bool
lemma_count n xs ys = count n (xs ++ ys) == (count n xs) + (count n ys)
|]

[lhp|genProp|reflect|admit
lemma_diseq :: NAT -> NAT -> Bool
lemma_diseq n m = n <= n+m
|]




{-======================================================
                  prop_04
=======================================================-}
[lhp|genProp|reflect|ple
prop_04 :: NAT -> [NAT] -> Bool
prop_04 n xs
  = (S (count n xs) == count n (n : xs))
|]



{-======================================================
                        prop_05
=======================================================-}
[lhp|genProp|reflect
prop_05 :: NAT -> NAT -> [NAT] -> Bool
prop_05 n x xs
  = (n == x) ==> (S (count n xs) == count n (x : xs))
|]

{-======================================================
                        prop_06
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpandP:1
prop_06 :: NAT -> NAT -> Bool
prop_06 n m = (n - (n + m) == Z)
|]

{-======================================================
                        prop_07
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpandP:1
prop_07 :: NAT -> NAT -> Bool
prop_07 n m = ((n + m) - n == m)
|]

{-======================================================
                        prop_08
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpandP:1
prop_08 :: NAT -> NAT -> NAT -> Bool
prop_08 k m n = ((k + m) - (k + n) == m - n)
|]


{-======================================================
                        prop_09
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpandP:2
prop_09 :: NAT -> NAT -> NAT -> Bool
prop_09 i j k
  = ((i - j) - k == i - (j + k))
|]



{-======================================================
                        prop_10
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand
prop_10 ::  NAT -> Bool
prop_10  m
  = (m - m == Z)
|]



{-======================================================
                        prop_11
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand
prop_11 ::  Eq a => [a] -> Bool
prop_11 xs
  = (drop Z xs == xs)
|]



{-======================================================
                    higherorder prop_12
=======================================================-}
-- [lhp|genProp|reflect|ple
-- prop_12 :: NAT -> NAT -> Bool
-- prop_12 n f xs
--   = (drop n (map f xs) === map f (drop n xs))
-- |]

{-======================================================
                        prop_13
=======================================================-}
[lhp|genProp|reflect|ple
prop_13 ::  NAT -> NAT -> [NAT] -> Bool
prop_13 n x xs
  = (drop (S n) (x : xs) == drop n xs)
|]

{-======================================================
                    higherorder prop_14
=======================================================-}
-- [lhp|genProp|reflect|ple
-- prop_14 :: NAT -> NAT -> Bool
-- prop_14 p xs ys
--   = (filter p (xs ++ ys) === (filter p xs) ++ (filter p ys))
-- |]





{-======================================================
                   prop_15 (hint-lemma)
=======================================================-}
-- rewrite error: Could not generate any rewrites from equality. Likely causes: 
--  - There are free (uninstantiatable) variables on both sides of the equality
--  - The rewrite would diverge

-- {-@ rewriteWith prop_15_proof [lemma_insert_proof] @-}
[lhp|genProp|reflect|ple
prop_15 ::  NAT -> [NAT] -> Bool
prop_15 n (x:xs) 
  | n<<x = trivial
  | otherwise = () ? prop_15_lemma_proof n x xs
-- the property:
prop_15 n ls = (length (insert n ls) == S (length ls))
|]

[lhp|genProp|inline|ple
prop_15_lemma :: NAT -> NAT -> [NAT] -> Bool
prop_15_lemma n x lls@(l:ls) 
          | n<<l = trivial
          | otherwise = () ? prop_15_lemma_proof n l ls
prop_15_lemma n x ls = length (insert n ls) == length (x:ls)
|]



{-======================================================
                 prop_16
=======================================================-}
[lhp|genProp|reflect
prop_16 :: NAT -> [NAT] -> Bool
prop_16 x xs
  = (xs == [] ) ==> (last (x:xs) == x)
|]



{-======================================================
                   prop_17
=======================================================-}
[lhp|genProp|reflect|ple
prop_17 ::  NAT -> Bool
prop_17 n = ((n <<= Z) == (n == Z))
|]



{-======================================================
                   prop_18
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpandP:1
prop_18 ::  NAT -> NAT -> Bool
prop_18 i m
  = (i << S (i + m))
|]

{-======================================================
                        prop_19
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand
prop_19 ::  NAT -> [NAT] -> Bool
prop_19 n xs
  = (length (drop n xs) == length xs - n)
|]



{-======================================================
                     prop_20 (hint-lemma-induction)
=======================================================-}
-- {-@ rewriteWith prop_20_proof [prop_20_lemma_proof] @-}
[lhp|genProp|inline|ple|caseExpand
prop_20 ::  [NAT] -> Bool
prop_20 ls@(x : xs)
  = ()
    ? prop_20_lemma_proof x xs
    ? prop_20_proof xs
-- property
prop_20 xs = (length (sort xs) == length xs)
|]

[lhp|genProp|inline|ple|admit
prop_20_lemma :: NAT -> [NAT] -> Bool
prop_20_lemma x xs = length (insort x (sort xs)) == S (length (sort xs))
|]

-- {-@ reflect prop_20 @-}
-- prop_20 :: [NAT] -> Bool
-- prop_20 xs = ((length (sort xs)) == length xs)

-- {-@ ple prop_20_proof @-}
-- {-@ rewriteWith prop_20_proof [prop_20_lemma_proof] @-}
-- {-@ prop_20_proof :: ns:[NAT] -> { prop_20 ns } @-}
-- prop_20_proof :: [NAT] -> Proof
-- prop_20_proof xs@[] = trivial

-- prop_20_proof ls@(x : xs)
--   = length (sort ls) == length ls 
--     ? prop_20_lemma_proof x xs
--     ? prop_20_proof xs

--   -- ?(length (sort ls)
--   -- === length (insort x (sort xs))
--   --   ? prop_20_lemma_proof x xs
--   -- === S (length (sort xs))
--   --   ? prop_20_proof xs
--   -- === S (length xs)
--   -- === length ls
--   -- )
--   *** QED




{-======================================================
                   prop_21
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpandP:1
prop_21 ::  NAT -> NAT -> Bool
prop_21 n m
  = (n <<= (n + m))
|]


{-======================================================
                     prop_22
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand
prop_22 ::  NAT -> NAT -> NAT -> Bool
prop_22 a b c
  = (max (max a b) c == max a (max b c))
|]



{-======================================================
                     prop_23
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand
prop_23 ::  NAT -> NAT -> Bool
prop_23 a b
  = (max a b == max b a)
|]



{-======================================================
                     prop_24
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand
prop_24 ::  NAT -> NAT -> Bool
prop_24 a b
  = ((max a b) == a) == (b <<= a)
|]



{-======================================================
                     prop_25
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand
prop_25 ::  NAT -> NAT -> Bool
prop_25 a b
  = ((max a b) == b) == (a <<= b)
|]



{-======================================================
                     prop_26
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpandP:2
prop_26 ::  NAT -> [NAT] -> [NAT] -> Bool
prop_26 x xs ys
  = (x `elem` xs) ==> (x `elem` (xs ++ ys))
|]



{-======================================================
                   prop_27
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpandP:2
prop_27 ::  NAT -> [NAT] -> [NAT] -> Bool
prop_27 x xs ys
  = (x `elem` ys) ==> (x `elem` (xs ++ ys))
|]






{-======================================================
                        prop_28
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand
prop_28 ::  NAT -> [NAT] -> Bool
prop_28 x xs
  = (x `elem` (xs ++ [x]))
|]

-}
{-======================================================
                     prop_29 (hint-induction)
=======================================================-}
[lhp|genProp|reflect|ple
prop_29 ::  NAT -> [NAT] -> Bool
prop_29 n ls@(x : xs)
  | n == x = trivial
  | otherwise = (n `elem` (ins1 n ls))
                    ? prop_29_proof n xs
  
-- the property:
prop_29 x xs
  = (x `elem` ins1 x xs)
|]

{-
{-======================================================
                      skipped prop_30
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_30 ::  NAT -> [NAT] -> Bool
prop_30 x xs
  = (x `elem` ins x xs)
|]


{-======================================================
                        prop_31
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand
prop_31 ::  NAT -> NAT -> NAT -> Bool
prop_31 a b c
  = (min (min a b) c == min a (min b c))
|]


{-======================================================
                        prop_32
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand
prop_32 ::  NAT -> NAT -> Bool
prop_32 a b
  = (min a b == min b a)
|]




{-======================================================
                      skipped prop_33
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_33 ::  NAT -> NAT -> Bool
prop_33 a b
  = (min a b == a) == (a <= b)
|]


{-======================================================
                      skipped prop_34
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_34 ::  NAT -> NAT -> Bool
prop_34 a b
  = (min a b == b) == (b <= a)
|]


{-======================================================
                      skipped prop_35
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_35 ::  [NAT] -> Bool
prop_35 xs
  = dropWhile (\ _ -> False) xs == xs
|]


{-======================================================
                      skipped prop_36
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_36 ::  [NAT] -> Bool
prop_36 xs
  = takeWhile (\ _ -> True) xs == xs
|]


{-======================================================
                      skipped prop_37
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_37 ::  NAT -> [NAT] -> Bool
prop_37 x xs
  = not (x `elem` delete x xs)
|]


{-======================================================
                        prop_38
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand
prop_38 ::  NAT -> [NAT] -> Bool
prop_38 n xs
  = count n (xs ++ [n]) == S (count n xs)
|]


{-======================================================
                        prop_39
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpandP:2
prop_39 ::  NAT -> NAT -> [NAT] -> Bool
prop_39 n x xs
  = count n [x] + count n xs == count n (x:xs)
|]




{-======================================================
                        prop_40
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand
prop_40 ::  [NAT] -> Bool
prop_40 xs
  = (take Z xs == [])
|]


{-======================================================
                      higherorder prop_41
=======================================================-}
-- [lhp|genProp|reflect|ple|induction|caseExpand|ignore
-- prop_41 ::  NAT -> [NAT] -> Bool
-- prop_41 n f xs
--   = (take n (map f xs) === map f (take n xs))
-- |]


{-======================================================
                        prop_42
=======================================================-}
[lhp|genProp|reflect
prop_42 ::  NAT -> NAT -> [NAT] -> Bool
prop_42 n x xs
  = (take (S n) (x:xs) == x : (take n xs))
|]


{-======================================================
                      higherorder prop_43
=======================================================-}
-- [lhp|genProp|reflect|ple|induction|caseExpand|ignore
-- prop_43 ::  NAT -> [NAT] -> Bool
-- prop_43 p xs
--   = (takeWhile p xs ++ dropWhile p xs === xs)
-- |]


{-======================================================
                        prop_44
=======================================================-}
[lhp|genProp|reflect
prop_44 ::  NAT -> [NAT] -> [NAT] -> Bool
prop_44 x xs ys
  = (zip (x:xs) ys == zipConcat x xs ys)
|]


{-======================================================
                        prop_45
=======================================================-}
[lhp|genProp|reflect
prop_45 ::  NAT -> NAT -> [NAT] -> [NAT] -> Bool
prop_45 x y xs ys
  = (zip (x:xs) (y:ys) == (x, y) : zip xs ys)
|]

{-======================================================
                        prop_46
=======================================================-}
[lhp|genProp|reflect
prop_46 :: [NAT] -> Bool
prop_46 xs
  = (zip ([]::[NAT]) xs == [])
|]



{-======================================================
                      skipped prop_47
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_47 ::  Tree a -> Bool
prop_47 a
  = (height (mirror a) == height a)
|]


{-======================================================
                      skipped prop_48
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_48 ::  [NAT] -> Bool
prop_48 xs
  = not (null xs) ==> (butlast xs ++ [last xs] == xs)
|]


{-======================================================
                      skipped prop_49
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_49 ::  [NAT] -> [NAT] -> Bool
prop_49 xs ys
  = (butlast (xs ++ ys) == butlastConcat xs ys)
|]


{-======================================================
                      skipped prop_50
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_50 ::  [NAT] -> Bool
prop_50 xs
  = (butlast xs == take (length xs - S Z) xs)
|]


{-======================================================
                        prop_51
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpandP:1
prop_51 ::  [NAT] -> NAT -> Bool
prop_51 xs x
  = (butlast (xs ++ [x]) == xs)
|]


{-======================================================
                      skipped prop_52
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_52 ::  NAT -> [NAT] -> Bool
prop_52 n xs
  = (count n xs == count n (rev xs))
|]

-- This property is the same as prod #50

{-======================================================
                      skipped prop_53
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_53 ::  NAT -> [NAT] -> Bool
prop_53 n xs
  = (count n xs == count n (sort xs))
|]


{-======================================================
                      skipped prop_54
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_54 ::  NAT -> NAT -> Bool
prop_54 n m
  = ((m + n) - n == m)
|]


{-======================================================
                        prop_55
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpandP:2
prop_55 ::  NAT -> [NAT] -> [NAT] -> Bool
prop_55 n xs ys
  = (drop n (xs ++ ys) == drop n xs ++ drop (n - length xs) ys)
|]


{-======================================================
                      skipped prop_56
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_56 ::  NAT -> NAT -> [NAT] -> Bool
prop_56 n m xs
  = (drop n (drop m xs) == drop (n + m) xs)
|]


{-======================================================
                        prop_57
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand
prop_57 ::  NAT -> NAT ->  [NAT] -> Bool
prop_57 n m xs
  = (drop n (take m xs) == take (m - n) (drop n xs))
|]


{-======================================================
                        prop_58
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand
prop_58 ::  NAT -> [NAT] -> [NAT] -> Bool
prop_58 n xs ys
  = (drop n (zip xs ys) == zip (drop n xs) (drop n ys))
|]


{-======================================================
                      skipped prop_59
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_59 ::  [NAT] -> [NAT] -> Bool
prop_59 xs ys
  = (ys == []) ==> (last (xs ++ ys) == last xs)
|]


{-======================================================
                      skipped prop_60
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_60 ::  [NAT] -> [NAT] -> Bool
prop_60 xs ys
  = not (null ys) ==> (last (xs ++ ys) == last ys)
|]


{-======================================================
                      skipped prop_61
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_61 ::  [NAT] -> [NAT] -> Bool
prop_61 xs ys
  = (last (xs ++ ys) == lastOfTwo xs ys)
|]


{-======================================================
                      skipped prop_62
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_62 ::  [NAT] -> NAT -> Bool
prop_62 xs x
  = not (null xs) ==> (last (x:xs) == last xs)
|]


{-======================================================
                      skipped prop_63
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_63 ::  NAT -> [NAT] -> Bool
prop_63 n xs
  = (n < length xs) ==> (last (drop n xs) == last xs)
|]


{-======================================================
                      skipped prop_64
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_64 ::  NAT -> [NAT] -> Bool
prop_64 x xs
  = (last (xs ++ [x]) == x)
|]


{-======================================================
                        prop_65
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_65 ::  NAT -> NAT -> Bool
prop_65 i m =
   i < S (m + i)
|]


{-======================================================
                      higherorder prop_66
=======================================================-}
-- [lhp|genProp|reflect|ple|induction|caseExpand|ignore
-- prop_66 ::  NAT -> [NAT] -> Bool
-- prop_66 p xs
--   =  length (filter p xs) <= length xs
-- |]


{-======================================================
                      skipped prop_67
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_67 ::  [NAT] -> Bool
prop_67 xs
  = (length (butlast xs) == length xs - S Z)
|]


{-======================================================
                      skipped prop_68
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_68 ::  NAT -> [NAT] -> Bool
prop_68 n xs
  = length (delete n xs) <= length xs
|]


{-======================================================
                      skipped prop_69
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_69 ::  NAT -> NAT -> Bool
prop_69 n m
  = n <= (m + n)
|]


{-======================================================
                      skipped prop_70
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_70 ::  NAT -> NAT -> Bool
prop_70 m n
  = m <= n ==> (m <= S n)
|]


{-======================================================
                      skipped prop_71
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_71 ::  NAT ->  NAT -> [NAT] -> Bool
prop_71 x y xs
  = ((x == y) == False) ==> (elem x (ins y xs) == elem x xs)
|]


{-======================================================
                      skipped prop_72
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_72 ::  NAT -> [NAT] -> Bool
prop_72 i xs
  = (rev (drop i xs) == take (length xs - i) (rev xs))
|]


{-======================================================
                      higherorder prop_73
=======================================================-}
-- [lhp|genProp|reflect|ple|induction|caseExpand|ignore
-- prop_73 ::  NAT -> [NAT] -> Bool
-- prop_73 p xs
--   = (rev (filter p xs) == filter p (rev xs))
-- |]


{-======================================================
                      skipped prop_74
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_74 ::  NAT -> [NAT] -> Bool
prop_74 i xs
  = (rev (take i xs) == drop (length xs - i) (rev xs))
|]


{-======================================================
                     prop_75
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand
prop_75 ::  NAT -> NAT -> [NAT] -> Bool
prop_75 n m xs
  = (count n xs + count n [m] == count n (m : xs))
|]


{-======================================================
                        prop_76
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpandP:3
prop_76 ::  NAT ->  NAT -> [NAT] -> Bool
prop_76 n m xs
  = ((n == m) == False) ==> (count n (xs ++ [m]) == count n xs)
|]

{-======================================================
                      skipped prop_77
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_77 ::  NAT -> [NAT] -> Bool
prop_77 x xs
  = sorted xs ==> sorted (insort x xs)
|]

{-======================================================
                      skipped prop_78
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_78 ::  [NAT] -> Bool
prop_78 xs
  = (sorted (sort xs))
|]


{-======================================================
                        prop_79
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpandP:2
prop_79 ::  NAT ->  NAT -> NAT -> Bool
prop_79 m n k
  = ((S m - n) - S k == (m - n) - k)
|]


{-======================================================
                        prop_80
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpandP:2
prop_80 ::  NAT ->  [NAT] -> [NAT] -> Bool
prop_80 n xs ys
  = (take n (xs ++ ys) == take n xs ++ take (n - length xs) ys)
|]


{-======================================================
                      skipped prop_81
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_81 ::  NAT ->  NAT -> [NAT] -> Bool
prop_81 n m xs 
  = (take n (drop m xs) == drop m (take (n + m) xs))
|]


{-======================================================
                        prop_82
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand
prop_82 ::  NAT ->  [NAT] -> [NAT] -> Bool
prop_82 n xs ys
  = (take n (zip xs ys) == zip (take n xs) (take n ys))
|]

{-======================================================
                        prop_83
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand
prop_83 :: [NAT] -> [NAT] -> [NAT]-> Bool
prop_83 xs ys zs
  = (zip (xs ++ ys) zs == zip xs (take (length xs) zs) ++ zip ys (drop (length xs) zs))
|]

{-======================================================
                        prop_84
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpandP:2
prop_84 :: [NAT] -> [NAT] -> [NAT] -> Bool
prop_84 xs ys zs
  = (zip xs (ys ++ zs) == zip (take (length ys) xs) ys ++ zip (drop (length ys) xs) zs)
|]

-- One way to prove this is to first show "Nick's lemma":
-- length xs = length ys ==> zip xs ys ++ zip as bs = zip (xs ++ as) (ys ++ bs)
{-======================================================
                      skipped prop_85
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_85 :: [NAT] -> [NAT] -> Bool
prop_85 xs ys
  = (length xs == length ys) ==> (zip (rev xs) (rev ys) == rev (zip xs ys))
|]


{-======================================================
                      skipped prop_86
=======================================================-}
[lhp|genProp|reflect|ple|induction|caseExpand|ignore
prop_86 :: NAT -> NAT -> [NAT] -> Bool
prop_86 x y xs
  = x < y ==> (elem x (ins y xs) == elem x xs)
|]


-----------------}

-- {-======================================================
--                     prop_03
-- =======================================================-}
-- {-@ reflect prople @-}
-- prople :: NAT -> NAT -> NAT -> Bool
-- prople n1 n2 n3 = (n1 <= n2) ==> (n1 <= n2 + n3)
-- {-@ prople_proof :: n1:NAT -> n2:NAT -> n3:NAT -> { prople n1 n2 n3 } @-}
-- prople_proof :: NAT -> NAT -> NAT -> Proof
-- prople_proof n1 n2 n3 = ()***Admit

-- {-@ reflect prop_03 @-}
-- prop_03 :: NAT -> [NAT] -> [NAT] -> Bool
-- prop_03 n xs ys = ((count n) xs) <= (count n) (xs ++ ys)
-- -- {-@ rewriteWith prop_03_proof [prop_02_proof] @-}
-- {-@ prop_03_proof :: n:NAT -> xs:[NAT] -> ys:[NAT] -> { prop_03 n xs ys } @-}
-- prop_03_proof :: NAT -> [NAT] -> [NAT] -> Proof
-- prop_03_proof n@Z xs ys
--   = (((count n) xs) <= (count n) (xs ++ ys)) 
--       ? prop_02_proof n xs ys
--  === (((count n) xs) <= (count n xs + count n ys))
--       ? prople_proof ((count n) xs) (count n xs) (count n ys)
--   *** QED
-- prop_03_proof n@(S p232) xs ys
--   = (((count n) xs) <= (count n) (xs ++ ys)
--        ? ((prop_03_proof p232) xs) ys)
--       *** Admit