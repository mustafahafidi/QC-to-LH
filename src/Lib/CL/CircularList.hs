{-# LANGUAGE  QuasiQuotes #-}
{- |
A simple purely functional circular list, or ring, data type.

Lets describe what we mean by 'ring'. A ring is a circular data structure
such that if you continue rotating the ring, you'll eventually return to
the element you first observed.

All of our analogies involve sitting at a table who's top surface rotates
about its center axis (think of those convenient rotating platforms one
often finds in an (Americanized) Chinese Restaurant).

Only the closest item on the table is avialable to us. In order to reach
other elements on the table, we need to rotate the table to the left or
the right.

Our convention for this problem says that rotations to the right are a
forward motion while rotations to the left are backward motions.

We'll use the following circular list for our examples:

>   8 7 6
>  9     5
> A       4
> B       3
>  C     2
>   D 0 1
>     ^

The pointer at the bottom represents our position at the table. The element
currently in front of is is referred to as the `focus`. So, in this case,
our focus is 0.

If we were to rotate the table to the right using the `rotR` operation, we'd
have the following table.

>   9 8 7
>  A     6
> B       5
> C       4
>  D     3
>   0 1 2
>     ^

This yields 1 as our new focus. Rotating this table left would return 0 to
the focus position.

-}
module Lib.CL.CircularList (
    -- * Data Types
    CList (..),
    -- foo,
    -- (=*=),
    -- * Functions
    -- ** Creation of CLists
    empty, toList, fromList, singleton,
    -- ** Update of CList
    update, reverseDirection,
    -- ** Converting CLists to Lists
    leftElements, rightElements, toInfList,
    -- ** Extraction and Accumulation
    focus, insertL, insertR,
    removeL, removeR,
    -- ** Manipulation of Focus
    allRotations, rotR, rotL, rotN, rotNR, rotNL, 
    mRotL, mRotR,
    rotateTo, findRotateTo,
    -- ** List-like functions
    filterR, filterL, foldrR, foldrL, foldlR, foldlL,
    -- ** Manipulation of Packing
    balance, packL, packR,
    -- ** Information
    isEmpty, size, 
) where
import TH.ProofGenerator
import Language.Haskell.Liquid.ProofCombinators

import Control.Applicative hiding (empty)
import Prelude hiding ( length, (++), reverse, cycle, iterate,splitAt
                        ,any)
import Data.List(find,foldl')
-- import Control.DeepSeq(NFData(..))
-- import Control.Monad(join)
import qualified Data.Traversable as T
import qualified Data.Foldable as F
import Lib.LH.Prelude
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen
-- import Language.Haskell.Liquid.ProofCombinators ((?))

{-@ LIQUID "--reflection"    @-}
{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--no-termination-check" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--no-adt" @-}

-- To convince LH of the safety of this file
{-@ ignore rotN @-}


-- | A functional ring type.
data CList a = Empty
             | CList [a] a [a]
             deriving (Eq, Show)

-- The same as Eq CList's (==)

{- Creating CLists -}
-- | An empty CList.
{-@ reflect empty @-}
{-@  empty :: {ls:CList a | ls==Empty && (size ls) == 0} @-}
empty :: CList a
empty = Empty -- ? (prop_empty Empty)



{- {-@ prop_empty ::ls:CList a -> { ls==Empty ==> (size ls) == 0} @-}
prop_empty :: CList a -> Proof
prop_empty Empty = size Empty ==. 0
                   ***QED
prop_empty cl = ()
  -}

-- |Starting with the focus, go right and accumulate all
-- elements of the CList in a list.

{-@ reflect rightElements @-}
{-@  rightElements::  cs:CList a -> {ls:[a] | (size cs) == (length ls)} @-}
rightElements :: CList a -> [a]
rightElements Empty = []
rightElements (CList l f r) = f : (r ++ (reverse l))




-- |Make a list from a CList.  
{-@ reflect toList @-}
{-@  toList:: cs:CList a -> {ls:[a] | (size cs) == (length  ls) } @-}
toList :: CList a -> [a]
toList = rightElements

-- |Make a (balanced) CList from a list.
{-@ reflect fromList @-}
{-@ fromList :: l:[a] -> { cl:CList a | (size cl) == (length l) } @-}
fromList :: [a] -> CList a
fromList [] = Empty
fromList a@(i:is) = let len = length a
                        (r,l) = splitAt (len `div` 2) is
                    in CList (reverse l) i r

-- {-@ singleton :: e:a -> {cl:CList a | toList cl == [e]} @-}

{-@ reflect singleton @-}
singleton :: a -> CList a
singleton e = CList [] e [] 
              -- ==. fromList [e]
              -- ==. fromList (toList (CList [] e []))


-- |Return the size of the CList.
{-@ measure size @-}
-- {-@ size :: cl:CList a -> {v:Int | length (toList cl) == v && v >= 0} @-}
size :: CList a -> Int
size Empty = 0
size (CList l _ r) = 1 + (length l) + (length r)




{- Updating of CLists -}

-- |Replaces the current focus with a new focus.
{-@ reflect update @-}
update :: a -> CList a -> CList a
update v Empty = CList [] v []
update v (CList l _ r) = CList l v r

-- |Reverse the direction of rotation.
{-@ reflect reverseDirection @-}
{-@ reverseDirection :: cl:CList a -> {rcl:CList a | size rcl == size cl} @-}
reverseDirection :: CList a -> CList a
reverseDirection Empty = Empty
reverseDirection (CList l f r) = CList r f l

{- Creating Lists -}
-- |Starting with the focus, go left and accumulate all
-- elements of the CList in a list.
leftElements :: CList a -> [a]
leftElements Empty = []
leftElements (CList l f r) = f : (l ++ (reverse r))

-- |Make a CList into an infinite list.
toInfList :: CList a -> [a]
toInfList = cycle . toList


{- Extraction and Accumulation -}

-- |Return the focus of the CList.
{-@ reflect focus @-}
focus :: CList a -> Maybe a
focus Empty = Nothing
focus (CList _ f _) = Just f

-- |Insert an element into the CList as the new focus. The
-- old focus is now the next element to the right.
{-@ reflect insertR @-}
{-@ insertR :: i:a-> cl:CList a -> {rl: CList a | size rl == size cl + 1 } @-}
insertR :: a -> CList a -> CList a
insertR i Empty = CList [] i []
insertR i (CList l f r) = CList l i (f:r)

-- |Insert an element into the CList as the new focus. The
-- old focus is now the next element to the left.
insertL :: a -> CList a -> CList a
insertL i Empty = CList [] i []
insertL i (CList l f r) = CList (f:l) i r

-- |Remove the focus from the CList. The new focus is the
-- next element to the left.
removeL :: CList a -> CList a
removeL Empty = Empty
removeL (CList [] _ []) = Empty
removeL (CList (l:ls) _ rs) = CList ls l rs
removeL (CList [] _ rs) = let (f:ls) = reverse rs
                          in CList ls f []



                            

-- |Remove the focus from the CList.
{-@ reflect removeR @-}
removeR :: CList a -> CList a
removeR Empty = Empty
removeR (CList [] _ []) = Empty
removeR (CList l _ (r:rs)) = CList l r rs
removeR (CList l _ []) = let (f:rs) = reverse l
                         in CList [] f rs

{- Manipulating Rotation -}

-- |Return all possible rotations of the provided 'CList', where the
-- focus is the provided 'CList'.
{-@ reflect allRotations @-}
allRotations :: CList a -> CList (CList a)
allRotations Empty = singleton Empty
allRotations cl = let 
                    ls = unfoldr (fmapLMaybe joinTuple . mRotL) cl
                    rs = unfoldr (fmapLMaybe joinTuple . mRotR) cl
                  in CList ls cl rs

-- >>> (fmapLMaybe joinTuple . mRotL ) (CList [] 0 [])
-- LNothing
--
{-@ reflect rotL @-}
rotL :: CList a -> CList a
rotL Empty = Empty
rotL r@(CList [] _ []) = r
rotL (CList (l:ls) f rs) = CList ls l (f:rs)
rotL (CList [] f rs) = let (l:ls) = reverse rs
                       in CList ls l [f]

-- |A non-cyclic version of 'rotL'; that is, only rotate the focus if
-- there is a previous (left) element to rotate to.
{-@ reflect mRotL @-}
mRotL :: CList a -> LMaybe (CList a)
mRotL (CList (l:ls) f rs) = LJust $ CList ls l (f:rs)
mRotL _ = LNothing

-- |Rotate the focus to the next (right) element.
{-@ reflect rotR @-}
-- {-@ rotR :: cl:CList a -> {l:CList a | rotL l == cl} @-}
rotR :: CList a -> CList a
rotR Empty = Empty
rotR r@(CList [] _ []) = r
rotR (CList ls f (r:rs)) = CList (f:ls) r rs
rotR (CList ls f []) = let (r:rs) = reverse ls
                       in CList [f] r rs

-- |A non-cyclic version of 'rotL'; that is, only rotate the focus if
-- there is a previous (left) element to rotate to.
{-@ reflect mRotR @-}
-- {-@ inline p @-}
-- p cl cr = True -- cl =*= cr
-- {-@ mRotR :: cr:CList a -> LMaybe {cl:(CList a) | p cl cr } @-}
mRotR :: CList a -> LMaybe (CList a)
mRotR (CList ls f (r:rs)) = LJust (CList (f:ls) r rs)
mRotR _ = LNothing

-- {-@ reflect foo @-}
-- {-@ foo :: Maybe {v:Int | v == 1 }  @-}
-- foo :: Maybe Int
-- foo = Just 1


-- |Rotate the focus the specified number of times; if the index is
-- positive then it is rotated to the right; otherwise it is rotated
-- to the left.
{-@ ignore rotN @-}
rotN :: Int -> CList a -> CList a
rotN _ Empty = Empty
rotN _ cl@(CList [] _ []) = cl
rotN n cl = iterate rot cl !! n'
  where
    n' = abs n
    rot | n < 0     = rotL
        | otherwise = rotR

-- |A wrapper around 'rotN' that doesn't rotate the CList if @n <= 0@.
rotNR :: Int -> CList a -> CList a
rotNR n cl
  | n <= 0 = cl
  | otherwise = rotN n cl

-- |Rotate the focus the specified number of times to the left (but
-- don't rotate if @n <= 0@).
rotNL :: Int -> CList a -> CList a
rotNL n cl
  | n <= 0 = cl
  | otherwise = rotN (negate n) cl

-- |Rotate the 'CList' such that the specified element (if it exists)
-- is focused.
rotateTo :: (Eq a) => a -> CList a -> Maybe (CList a)
rotateTo a = findRotateTo (a==)

-- |Attempt to rotate the 'CList' such that focused element matches
-- the supplied predicate.
findRotateTo :: (a -> Bool) -> CList a -> Maybe (CList a)
findRotateTo p = find (maybe False p . focus) . toList . allRotations

{- List-like functions -}

-- |Remove those elements that do not satisfy the supplied predicate,
-- rotating to the right if the focus does not satisfy the predicate.
filterR :: (a -> Bool) -> CList a -> CList a
filterR = filterCL removeR

-- |As with 'filterR', but rotates to the /left/ if the focus does not
-- satisfy the predicate.
filterL :: (a -> Bool) -> CList a -> CList a
filterL = filterCL removeL

-- |Abstract away what to do with the focused element if it doesn't
-- match the predicate when filtering.
filterCL :: (CList a -> CList a) -> (a -> Bool) -> CList a -> CList a
filterCL _ _ Empty = Empty
filterCL rm p (CList l f r)
  | p f = cl'
  | otherwise = rm cl'
  where
    cl' = CList (filter p l) f (filter p r)

-- |A right-fold, rotating to the right through the CList.
foldrR :: (a -> b -> b) -> b -> CList a -> b
foldrR = foldrCL rightElements

-- |A right-fold, rotating to the left through the CList.
foldrL :: (a -> b -> b) -> b -> CList a -> b
foldrL = foldrCL leftElements

-- |Abstract away direction for a foldr.
foldrCL :: (CList a -> [a]) -> (a -> b -> b) -> b -> CList a -> b
foldrCL toL f a = foldr f a . toL

-- |A (strict) left-fold, rotating to the right through the CList.
foldlR :: (a -> b -> a) -> a -> CList b -> a
foldlR = foldlCL rightElements

-- |A (strict) left-fold, rotating to the left through the CList.
foldlL :: (a -> b -> a) -> a -> CList b -> a
foldlL = foldlCL leftElements

-- |Abstract away direction for a foldl'.
foldlCL :: (CList b -> [b]) -> (a -> b -> a) -> a -> CList b -> a
foldlCL toL f a = foldl' f a . toL

{- Manipulating Packing -}

-- |Balance the CList. Equivalent to `fromList . toList`
balance :: CList a -> CList a
balance = fromList . toList

-- |Move all elements to the left side of the CList.
{-@ reflect packL @-}
packL :: CList a -> CList a
packL Empty = Empty
packL (CList l f r) = CList (l ++ (reverse r)) f []

-- |Move all elements to the right side of the CList.
{-@ reflect packR @-}
packR :: CList a -> CList a
packR Empty = Empty
packR (CList l f r) = CList [] f (r ++ (reverse l))

{- Information -}

-- |Returns true if the CList is empty.
{-@ reflect isEmpty @-}
isEmpty :: CList a -> Bool
isEmpty Empty = True
isEmpty _ = False

{- Instances -}
{- 
instance (Show a) => Show (CList a) where
 showsPrec d cl  = showParen (d > 10) $
                   showString "fromList " . shows (toList cl)
 -}
instance (Read a) => Read (CList a) where
 readsPrec p = readParen (p > 10) $ \ r -> do
   ("fromList",s) <- lex r
   (xs,t) <- reads s
   return (fromList xs,t)


-- instance (Eq a) => Eq (CList a) where
--   a == b = any ((toList a ==) . toList) . toList $ allRotations b

-- instance (NFData a) => NFData (CList a) where
--   rnf Empty         = ()
--   rnf (CList l f r) = rnf f
--                       `seq` rnf l
--                       `seq` rnf r

instance Arbitrary a => Arbitrary (CList a) where
    arbitrary = frequency [(1, return Empty), (10, arbCList)]
        where arbCList = do
                l <- arbitrary
                f <- arbitrary
                r <- arbitrary
                return $ CList l f r
    shrink (CList l f r) = Empty : [ CList l' f' r' | l' <- shrink l,
                                                      f' <- shrink f,
                                                      r' <- shrink r]
    shrink Empty = []

instance Functor CList where
    fmap _ Empty = Empty
    fmap fn (CList l f r) = (CList (fmap fn l) (fn f) (fmap fn r))

instance F.Foldable CList where
  foldMap = T.foldMapDefault

instance T.Traversable CList where
  -- | traverses the list from left to right, starting at the focus
  traverse _ Empty         = pure Empty
  traverse g (CList l f r) = (\f' r' l' -> CList l' f' r') <$> g f
                                                           <*> T.traverse g r
                                                           <*> T.traverse g l
 





{- 
[lhp|genProp|reflect|ple

lemma_refl :: Eq a => CList a -> Bool
lemma_refl cl@Empty =  cl =*= cl
                ?(Empty =*= (Empty::CList Int) 
                === ( any ((toList Empty ==) . toList) . toList $ allRotations (Empty::CList Int) )
                === ( (\ls -> any ((toList Empty ==) . toList) (toList ls)) $ allRotations (Empty::CList Int) )
                === ( (\ls -> any ((toList Empty ==) . toList) (toList ls)) (allRotations (Empty::CList Int)) )
                === ( any ((toList Empty ==) . toList) (toList (allRotations (Empty::CList Int))) ) -- def of allRotations
                ===  any ((toList Empty ==) . toList) (toList (singleton (Empty::CList Int))) 
                ===  any ((toList Empty ==) . toList) (toList ((CList [] (Empty::CList Int) []))) 
                ===  any ((toList Empty ==) . toList) (rightElements (CList [] (Empty::CList Int) [])) 
                ===  any ((toList Empty ==) . toList) ((Empty::CList Int) : ([] ++ (reverse [])))  -- expanding reverse
                                                                        ? (([] ++ (reverse []))
                                                                        === ([] ++ ([]))
                                                                        === []
                                                                        )
                === any ((toList Empty ==) . toList) ((Empty::CList Int) : ([])) 
                === any ((toList Empty ==) . toList) [Empty::CList Int]
        --   def. of any
                === (((toList Empty ==) . toList) (Empty :: CList Int) || any ((toList (Empty :: CList Int) ==) . toList) [])
                ==! True)
lemma_refl cl = cl =*= cl
                ?(()***Admit)

|]
 -}
{- 
{-@ LIQUID "--ple-local" @-}

{-@ reflect =*= @-}
{-@ infix 4 =*= @-}
(=*=) :: Eq a  => CList a -> CList a -> Bool
a =*= b = any ((toList a ==) . toList)  (toList ( singleton b)) --(any ((toList a ==) . toList) . toList $ allRotations b)


{-@ reflect lemma_refl @-}
lemma_refl :: Eq a => CList a -> Bool
lemma_refl cl = cl =*= cl

{-@ ple  lemma_refl_proof @-}
{-@ lemma_refl_proof :: Eq a => cl:CList a -> { lemma_refl cl } @-}
lemma_refl_proof :: Eq a => CList a -> Proof
lemma_refl_proof cl@Empty
  = cl =*= cl
       ? (lemma_refl cl 
       === cl =*= cl
      --  ===( any (\x -> toList cl == toList x)  (toList (allRotations cl)))

      --                                       ? ( (toList (allRotations cl))
      --                                       ===  toList (singleton cl)
      --                                       ===  toList (CList [] Empty [])
      --                                       ===  rightElements (CList [] Empty [])
      --                                       ===  Empty : ([] ++ (reverse []))
      --                                       ===  Empty : ([])
      --                                       ===  [Empty]

                                            
      --                                       )
      --  === ( any ((toList cl ==) . toList )  ([Empty]))
            -- ===
            --   ((any ((toList Empty ==) . toList)) . toList
            --      $ allRotations (Empty :: CList Int))
            -- ===
            --   ((\ ls -> (any ((toList Empty ==) . toList)) (toList ls))
            --      $ allRotations (Empty :: CList Int))
            -- ===
            --   ((\ ls -> (any ((toList Empty ==) . toList)) (toList ls))
            --      (allRotations (Empty :: CList Int)))
            -- ===
            --   ((any ((toList Empty ==) . toList))
            --      (toList (allRotations (Empty :: CList Int))))
            -- ===
            --   (any ((toList Empty ==) . toList))
            --     (toList (singleton (Empty :: CList Int)))
            -- ===
            --   (any ((toList Empty ==) . toList))
            --     (toList ((((CList []) (Empty :: CList Int)) [])))
            -- ===
            --   (any ((toList Empty ==) . toList))
            --     (rightElements (((CList []) (Empty :: CList Int)) []))
            -- ===
            --   (any ((toList Empty ==) . toList))
            --     ((Empty :: CList Int) : ([] ++ (reverse [])))
            -- ? (([] ++ (reverse [])) === ([] ++ ([])) === [])
            -- ===
            --   (any ((toList Empty ==) . toList)) ((Empty :: CList Int) : ([]))
            -- === (any ((toList Empty ==) . toList)) [Empty :: CList Int]
            -- ===
            --   ((((toList Empty ==) . toList) (Empty :: CList Int))
            --      || (any ((toList (Empty :: CList Int) ==) . toList)) [])
            )

      *** Admit
lemma_refl_proof cl = (cl =*= cl ? (() *** Admit)) *** QED
 -}


-- {-@ LIQUID "--ple-local" @-}
-- {-@ reflect toListRef @-}
-- toListRef :: CList a -> [a]
-- toListRef Empty = []
-- toListRef (CList l f r) = f : (r ++ (reverse l))


-- {-@ reflect eqToList @-}
-- eqToList ::  CList Int -> CList Int -> Bool
-- eqToList a b = True

-- {-@ reflect =*= @-}
-- {-@ infix 4 =*= @-}
-- (=*=) :: CList Int -> CList Int -> Bool
-- x =*= Empty = (any (eqToList x) ((toListRef (allRotations Empty))))
-- x =*= (CList l f r) = (any (eqToList x) (toListRef (allRotations (CList l f r))))

-- {-@ reflect lemma_refl @-}
-- lemma_refl :: Bool
-- lemma_refl = Empty =*= Empty

-- {-@ ple lemma_refl_proof @-}
-- {-@ lemma_refl_proof ::  { lemma_refl  } @-}
-- lemma_refl_proof :: Proof
-- lemma_refl_proof = lemma_refl
--                 -- === Empty =*= Empty
--                 -- === (any (eqToList Empty) [])
--                 -- === False
--             *** QED
