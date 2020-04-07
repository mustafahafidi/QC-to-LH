module Digits
    ( mDigits
    , digits
    , mDigitsRev
    , digitsRev
    , unDigits
    -- , prop_digitsRoundTrip
    )
where
import           Equational

import           Test.QuickCheck
-- import           Data.Maybe                     ( fromJust )
import           Data.List                      ( genericTake )
import Prelude hiding (foldl, reverse, (++), (.))


{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--exact-data-con" @-}

{-@ data Maybe a = Nothing | Just a @-}
{-@ reflect fromJust @-}
fromJust :: Maybe a -> a
fromJust (Just a) = a

{-# INLINE (.) #-}

{-@ reflect . @-}
(.)    :: (b -> c) -> (a -> b) -> a -> c
(.) f g = \x -> f (g x)

{-@ infix   ++ @-}
{-@ reflect ++ @-}
(++) :: [a] -> [a] -> [a]
[]       ++ ys = ys
(x : xs) ++ ys = x : (xs ++ ys)

{-@ reflect reverse @-}
reverse :: [a] -> [a]
reverse []       = []
reverse (x : xs) = (reverse xs) ++ [x]

{-@ reflect foldl @-}
foldl :: (b -> a -> b) -> b -> [a] -> b 
foldl f b []        = b 
foldl f b (x:xs) = foldl f (f b x) xs

-- LIBRARY CODE


{-@ reflect mDigitsRev @-}
mDigitsRev
    :: Integral n
    => n         -- ^ The base to use.
    -> n         -- ^ The number to convert to digit form.
    -> Maybe [n] -- ^ Nothing or Just the digits of the number in list form, in reverse.
    
mDigitsRev base i = if base < 1
    then Nothing -- We do not support zero or negative bases
    else Just $ dr base i
  where
    dr _ 0 = []
    dr b x = case base of
        1 -> genericTake x $ repeat 1
        _ -> let (rest, lastDigit) = quotRem x b in lastDigit : dr b rest

-- | Returns the digits of a positive integer as a Maybe list.
--   or Nothing if a zero or negative base is given
{-@ reflect mDigits @-}
mDigits
    :: Integral n
    => n -- ^ The base to use.
    -> n -- ^ The number to convert to digit form.
    -> Maybe [n] -- ^ Nothing or Just the digits of the number in list form
mDigits base i = reverse <$> mDigitsRev base i



{-@ reflect digitsRev @-}
-- | Returns the digits of a positive integer as a list, in reverse order.
--   Throws an error if given a zero or negative base.
digitsRev
    :: Integral n
    => n   -- ^ The base to use.
    -> n   -- ^ The number to convert to digit from.
    -> [n] -- ^ The digits of the number in list from, in reverse.
digitsRev base = fromJust . mDigitsRev base

-- | Returns the digits of a positive integer as a list.
--   Throws an error if given a zero or negative base.
{-@ reflect digits @-}
digits
    :: Integral n
    => n   -- ^ The base to use (typically 10).
    -> n   -- ^ The number to convert to digit form.
    -> [n] -- ^ Either Nothing or the digits of the number in list form.
digits base = reverse . digitsRev base


{-@ reflect unDigits @-}
-- | Takes a list of digits, and converts them back into a positive integer.
unDigits
    :: Integral n
    => n   -- ^ The base to use.
    -> [n] -- ^ The digits of the number in list form.
    -> n   -- ^ The original number.
unDigits base = foldl (\a b -> a * base + b) 0

-- | unDigits . digits should be the identity, in any positive base.
prop_digitsRoundTrip
    :: Integer -- ^ The integer to test.
    -> Integer -- ^ The base to use.
    -> Property
prop_digitsRoundTrip i b = i > 0 ==> b > 0 ==> i == (unDigits b . digits b) i


{-@ digitsRoundTrip :: {b:Int | b>0} -> {i:Int | i>0} -> { i = 1} @-}
digitsRoundTrip :: Int -> Int -> Proof
digitsRoundTrip b i = 
                    i ==. (unDigits b . digits b) i
                     *** QED


main = do
    print $ unDigits 10 [1, 0, 0]
    return $ digits 10 100
