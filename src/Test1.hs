module Test1 where
import Language.Haskell.Liquid.Prelude
import Prelude  hiding (length, 
                        (++), 
                        reverse, 
                        iterate, 
                        null, 
                        splitAt,
                        any
                    -- ,($)
                        )
import Data.List (find)
import Lib.LH.Prelude -- hiding (LMaybe(..))
import Lib.CL.CircularList --hiding (mRotR)
import Language.Haskell.Liquid.ProofCombinators

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-totality" @-}
-- {-@ LIQUID "--higherorder" @-}


-- {-@ reflect foo @-}
-- foo :: Maybe Int
-- foo = Just $ 1
-- {-@ wFoo :: Maybe {v:Int | v == 1 } @-}
-- wFoo = foo

{-@ reflect =*= @-}
{-@ infix 4 =*= @-}
(=*=) :: Eq a  => CList a -> CList a -> Bool
a =*= b =  any ((toList a ==) . toList) . toList $ allRotations b


-- {-@ reflect mRotR @-}
-- {-@ Lib.CL.CircularList.mRotR :: cr:CList a -> LMaybe {cl:(CList a) | p cl cr } @-}

{-@ inline test @-}
test = case mRotR ((CList [] 0 [])::CList Int) of
                LJust cl -> cl =*= Empty
                LNothing -> True

{-@ inline p @-}
p cl cr =  cl =*= cr
{-@ wMRotR :: cr:CList a -> LMaybe {cl:(CList a) | p cl cr } @-} -- without the wrapper, assumes the type
wMRotR cl@(CList ls f (r:rs)) = mRotR cl
                           === LJust (CList (f:ls) r rs)
                           ? (
                               cl =*=  (CList (f:ls) r rs)
                           ***Admit
                           )
                           
-- wMRotR cl@_ = mRotR cl
--             === LNothing 
            
            --    ?(cl =*= ***Admit)

{-@ inline p2 @-}
p2 cl LNothing =  True
p2 cl (LJust cr) =  cl =*= cr
{-@ lemma_rot :: cl:CList a -> { p2 cl (mRotR cl) } @-}
lemma_rot :: Eq a => CList a -> Proof
lemma_rot cl = p2 cl (mRotR cl)
            
             ***QED
 