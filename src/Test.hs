module Test where
import Language.Haskell.Liquid.Prelude
import Prelude  hiding (length, 
                        (++), 
                        reverse, 
                        iterate, 
                        null, 
                        splitAt,
                        any
                        
                        )
import Data.List (find)
import Lib.LH.Prelude 
import Lib.CL.CircularList
import Language.Haskell.Liquid.ProofCombinators

{-@ LIQUID "--reflection"    @-}
{-@ LIQUID "--short-names"    @-}






{-@ reflect =*= @-}
{-@ infix 4 =*= @-}
(=*=) :: Eq a  => CList a -> CList a -> Bool
a =*= b =  any ((toList a ==) . toList) . toList $ allRotations b




{-@ inline p1 @-}
p1 = (CList [] 0 [1] =*= CList [0] 1 [])

{-@ inline p2 @-}
p2  = (CList [] 0 [] =*= CList [] 0 [])

{-@ inline p3 @-}
p3  = (Empty =*= (Empty::CList Int))

{-======================================================
                        proving p1
=======================================================-}
{-@ p1_proof ::  {p1} @-}
p1_proof ::  Proof
p1_proof =  (CList [] 0 [1] =*= CList [0] 1 [])
                ? (
                    mRotR (CList [] 0 [1])
                === LJust (CList [0] 1 [])
                )
                ? lemma_rotR (CList [] 0 [1])
        ***QED
        

{-======================================================
                        proving p2
=======================================================-}
{-@ p2_proof ::  {p2} @-}
p2_proof ::  Proof
p2_proof = lemma_refl (CList [] 0 [])
        

{-======================================================
                        proving p3
=======================================================-}
{-@ p3_proof ::  { p3 } @-}
p3_proof ::  Proof
p3_proof = lemma_refl (Empty::CList Int)
        



{-======================================================
               START LEMMAS
=======================================================-}
-- Distributivity of `any` over `++`
{-@ inline lemma_any_p @-}
lemma_any_p p ls rs = any p (ls++rs) == ((any p ls) || (any p rs))
{-@ lemma_any :: p:(a->Bool) -> ls:[a] -> rs:[a] -> { lemma_any_p p ls rs } @-}
lemma_any :: (a->Bool) -> [a] -> [a] -> Proof
lemma_any p [] rs = ( any p ([]++rs))
                === ( any p rs)
                === ( any p [] || any p rs)
                ***QED

lemma_any p (l:ls) rs = ( any p ((l:ls)++rs))
                    === ( any p (l:(ls++rs)))
                    === ( p l || any p (ls++rs))
                                    ? lemma_any p ls rs
                    === ( p l || (any p ls) || (any p rs))
                    === ( (any p (l:ls)) || (any p rs))
                    ***QED

{-@ inline prm2 @-}
prm2 cl LNothing =  True
prm2 cl (LJust cr) =  cl =*= cr

-- CList semantic preserving for right rotation (mRotR)
{-@ lemma_rotR :: cl:CList a -> { prm2 cl (mRotR cl) } @-}
lemma_rotR :: Eq a => CList a -> Proof
lemma_rotR cl@(CList ls f (r:rs)) =  prm2 cl (mRotR cl)
                                === prm2 cl (LJust (CList (f:ls) r rs))
                                === cl =*= (CList (f:ls) r rs)
                                === (any ((toList cl ==) . toList) . toList $ allRotations (CList (f:ls) r rs))
                                === ((\x-> any ((toList cl ==) . toList) (toList x)) $ allRotations (CList (f:ls) r rs))
                                === (any ((toList cl ==) . toList) (toList  (allRotations (CList (f:ls) r rs))))
                                -- def of allRotations
                                === ( let   rls_x  = (CList ls f (r:rs))
                                            rls_xs = unfoldr (fmapLMaybe joinTuple . mRotL) (CList ls f (r:rs))

                                            rls =  unfoldr (fmapLMaybe joinTuple . mRotL) (CList (f:ls) r rs) -- def of unfoldr
                                                ? (
                                                    (fmapLMaybe joinTuple . mRotL)  (CList (f:ls) r rs)
                                                === fmapLMaybe joinTuple (mRotL (CList (f:ls) r rs))
                                                === fmapLMaybe joinTuple (LJust (CList ls f (r:rs)))
                                                === (LJust (joinTuple (CList ls f (r:rs))))
                                                === (LJust (rls_x,rls_x))
                                                )
                                             === (rls_x : rls_xs)
                                        
                                            rrs =  unfoldr (fmapLMaybe joinTuple . mRotR) (CList (f:ls) r rs)

                                      in     (any ((toList cl ==) . toList) (toList (CList rls (CList (f:ls) r rs) rrs ) ))
                                         === (any ((toList cl ==) . toList) (rightElements (CList rls (CList (f:ls) r rs) rrs ) ))
                                         === (any ((toList cl ==) . toList) ((CList (f:ls) r rs) : (rrs ++ (reverse rls))) )
                                          --  def of any
                                         === ( let p = ((toList cl ==) . toList)
                                                   first = (CList (f:ls) r rs)
                                               in  (p first || any p (rrs ++ (reverse rls)))
                                                --  def of reverse
                                               === (p first || any p (rrs ++ (reverse rls_xs ++ [rls_x])))
                                                              ? lemma_any p rrs  (reverse rls_xs ++ [rls_x])
                                               === (p first || (any p rrs || any p (reverse rls_xs ++ [rls_x])))
                                                                            ? lemma_any p (reverse rls_xs) [rls_x]
                                               === (p first || (any p rrs || (any p (reverse rls_xs) || any p [rls_x])))
                                                                                                    ? (
                                                                                                        any p [rls_x]
                                                                                                    === ( ((toList cl ==) . toList) rls_x || any p [] )
                                                                                                    === ( (toList cl ==)  (toList rls_x) )
                                                                                                    === ( toList cl == toList rls_x )
                                                                                                    )
                                             )
                                     )
                                ***QED
 
lemma_rotR cl@_ =  prm2 cl (mRotR cl)
            === prm2 cl (LNothing)
             ***QED
 
-- CList semantic preserving for left rotation (mRotL)
{-@ lemma_rotL :: cl:CList a -> { prm2 cl (mRotL cl) } @-}
lemma_rotL :: Eq a => CList a -> Proof
lemma_rotL cl@(CList (l:ls) f rs) =  prm2 cl (mRotL cl)
                                === prm2 cl (LJust (CList ls l (f:rs)))
                                === cl =*= (CList ls l (f:rs))
                                === (any ((toList cl ==) . toList) . toList $ allRotations  (CList ls l (f:rs)) )
                                === ((\x-> any ((toList cl ==) . toList) (toList x)) $ allRotations (CList ls l (f:rs)) )
                                === (any ((toList cl ==) . toList) (toList  (allRotations  (CList ls l (f:rs)))))
                                -- def of allRotations
                                === ( let  
                                            rls =  unfoldr (fmapLMaybe joinTuple . mRotL) (CList ls l (f:rs))

                                            rrs_x  = (CList (l:ls) f rs)
                                            rrs_xs = unfoldr (fmapLMaybe joinTuple . mRotR) (CList (l:ls) f rs)
                                            rrs =  unfoldr (fmapLMaybe joinTuple . mRotR) (CList ls l (f:rs)) -- def of unfoldr
                                                ? (
                                                    (fmapLMaybe joinTuple . mRotR)  (CList ls l (f:rs))
                                                === fmapLMaybe joinTuple (mRotR  (CList ls l (f:rs)))
                                                === fmapLMaybe joinTuple (LJust (CList (l:ls) f rs))
                                                === (LJust (joinTuple (CList (l:ls) f rs)))
                                                === (LJust (rrs_x,rrs_x))
                                                )
                                               === (rrs_x : rrs_xs)

                                      in     (any ((toList cl ==) . toList) (toList (CList rls (CList ls l (f:rs)) rrs ) ))
                                         === (any ((toList cl ==) . toList) (rightElements (CList rls (CList ls l (f:rs)) rrs ) ))
                                         === (any ((toList cl ==) . toList) ((CList ls l (f:rs)) : (rrs ++ (reverse rls))) )
                                          --  def of any
                                         === ( let p = ((toList cl ==) . toList)
                                                   first = (CList ls l (f:rs))
                                               in  (p first || any p (rrs ++ (reverse rls)))
                                                --  def of reverse
                                               === (p first || any p (rrs ++ (reverse rls)))
                                                              ? lemma_any p rrs  (reverse rls)
                                               === (p first || (any p rrs || any p (reverse rls)))
                                                                ? (
                                                                    any p rrs
                                                                === ( ((toList cl ==) . toList) rrs_x || any p rrs_xs )
                                                                === ( ((toList cl ==) . toList) rrs_x || any p rrs_xs )
                                                                === ( (toList cl ==)  (toList rrs_x) || any p rrs_xs )
                                                                === ( toList cl == toList rrs_x || any p rrs_xs)
                                                                )
                                             )
                                     )
                                ***QED
 
lemma_rotL cl@_ =  prm2 cl (mRotL cl)
            === prm2 cl (LNothing)
             ***QED
 
 

---- Reflexivity of (=*=)
{-@ inline refl @-}
refl cl = cl =*= cl
{-@ lemma_refl ::  Eq a => cl:CList a -> { refl cl} @-}
lemma_refl :: Eq a =>  CList a -> Proof
lemma_refl Empty = Empty =*= (Empty::CList Int)
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
                ***QED
lemma_refl cl@(CList l f r) = refl cl 
                           === cl =*= cl
                           === ( any ((toList cl ==) . toList) . toList $ allRotations cl) -- def. allRotations
                           === ( let  ls =  unfoldr (fmapLMaybe joinTuple . mRotL) cl
                                      rs =  unfoldr (fmapLMaybe joinTuple . mRotR) cl
                                 in     ( (\ls -> any ((toList cl ==) . toList) (toList ls)) $ CList ls cl rs )
                                    === ( any ((toList cl ==) . toList) (toList (CList ls cl rs)) )
                                    === ( any ((toList cl ==) . toList) (rightElements (CList ls cl rs)) )
                                    === ( any ((toList cl ==) . toList) (cl : (rs ++ (reverse ls))) ) 
                                    -- def of any
                                    === ( let p = (((toList cl ==) . toList))
                                              (x:xs) = (cl : (rs ++ (reverse ls)))
                                         in (p x || any p xs )
                                          === (toList cl == toList x || any p xs )
                                         )
                               )
                           ***QED

{-======================================================
                END LEMMAS
=======================================================-}       
