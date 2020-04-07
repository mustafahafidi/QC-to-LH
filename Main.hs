module Reverse where
import           Test.QuickCheck
import           Prelude                 hiding ( (++)
                                                , sum
                                                , const
                                                , id
                                                )

{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--exact-data-con" @-}

{- 
{-@  fac :: n:Nat -> Nat   @-}
fac :: Int -> Int
fac 0 = 1
fac n = n * fac (n - 1)


{-@ type List a = [a] @-}
{-@ type ListN a N = {v:List a | size v = N} @-}
{-@ type ListX a X = ListN a { size X }        @-}

 -}



{- const FUNCTION -}
prop_const :: Int -> Bool
prop_const a = (const a) == 1

{-@ const :: a:_ -> {v:Int | v = 1} @-}
const :: a -> Int
const _ = 1


{-@ proof :: a:a -> {const a = 1} @-}
proof :: a -> ()
(const a) == 1

{- 
- 
- find a library that uses quickcheck to take into consideration (smaller than xmonad)
- xmonad quickcheck tests
16:30 weekly calls
 -}


{- SUM two params FUNCTION -}
prop_sum :: Int -> Int -> Bool
prop_sum a b = (sum a b) == a + b

{-@ sum :: a:Int -> b:Int -> {v:Int | v = a + b} @-}
sum :: Int -> Int -> Int
sum a b = a + b








{- Length FUNCTION -}

{-@ measure size @-}
size :: [a] -> Int
size []       = 0
size (_ : xs) = 1 + size xs

prop_len :: [Int] -> Bool
prop_len xs = (len xs) == (size xs) -- transform "size" to a measure (or reflect it) then used it in the refinement type

{-@ len :: ls:[a] -> {v:Int | v == size ls } @-}
len :: [a] -> Int
len []       = 0
len (_ : xs) = 1 + len xs









{- Identity function -}

prop_id :: [Int] -> Bool
prop_id xs = (id xs) == xs

{-@ id :: v:_ -> {r:_ | r = v }@-}
id :: a -> a
id x = x

prop_id2 xs = id (id xs) == xs -- here double application, need reflection ?






prop_len1 :: [Int] -> Bool
prop_len1 xs = (len xs) == (size xs)

-- {-@ len1 :: ls:[a] -> {v:Int | v == size ls } @-}
len1 :: [a] -> Int
len1 xs = go xs 0
 where
  go []       acc = acc
  go (x : xs) acc = go xs (acc + 1)








{- REVERSE FUNCTION -}
{-@ infix   ++ @-}
{-@ reflect ++ @-}
(++) :: [a] -> [a] -> [a]
[]       ++ ys = ys
(x : xs) ++ ys = x : (xs ++ ys)

{-@ reflect rev @-}
rev :: [a] -> [a]
rev []       = []
rev (x : xs) = (rev xs) ++ [x]


prop_reverse :: [Int] -> Bool
prop_reverse xs = reverse (reverse xs) == xs


{-@ reverseCust :: is:[a] -> {rs:[a] | true } @-}
reverseCust ls = go ls []
 where
  go []       acc = acc
  go (x : xs) acc = go xs (x : acc)





main :: IO ()
main = do
  {- print "Insert list to reverse: "
  l <- getLine
  let list = read l :: [Int]
  putStrLn $ "Reversed List: " ++ show (reverseCust list) -}
  quickCheck prop_sum
  quickCheck prop_len
  quickCheck prop_len1
  quickCheck prop_reverse
