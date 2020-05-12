module Lib.CL.ExtraTheorems where
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
a =*= b =  (any ((toList a ==) . toList) . toList $ allRotations b)

{-======================================================
               START LEMMAS
=======================================================-}
-- Distributivity of `any` over `++`
{-@ inline lemma_any_p @-}
lemma_any_p p ls rs = any p (ls++rs) == ((any p ls) || (any p rs))
{-@ lemma_any :: p:(a->Bool) -> ls:[a] -> rs:[a] -> { lemma_any_p p ls rs } @-}
lemma_any :: (a->Bool) -> [a] -> [a] -> Proof
lemma_any p ls rs = True ***Admit

{- 
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
 
  -}

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

{-

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
        
 -}
{- 
 {-@ inline prop_list_p@-}
prop_list_p c = c =*= (fromList . toList $ c)

{-@ prop_list :: c:CList Int -> { prop_list_p c } @-}
prop_list :: CList Int -> Proof
prop_list c@Empty = (c =*= (fromList . toList $ c))
                      ? (
                      c === Empty
                      === (fromList [])
                      === (fromList (rightElements Empty))
                      === (fromList (toList Empty))
                      === (fromList (toList  c))
                      )
                      ? lemma_refl (Empty::CList Int)
                === c =*= Empty
                     ***QED

prop_list c@(CList l f r) = c =*= (fromList . toList $ c)
                                    ?( 
                                        (fromList (toList c))
                                        === (fromList (rightElements c))
                                        === (fromList (f : (r ++ (reverse l))))
                                    )
                         ===  (let 
                                a@(i:is) = f : (r ++ (reverse l))
                                len = length a
                                (sr,sl) = splitAt (len `div` 2) is -- is = sr++sl
                            in    c =*= (CList (reverse sl) f sr)
                              === (any ((toList c ==) . toList) . toList $ allRotations (CList (reverse sl) f sr))
                            )
                        ***Admit  
  -}


{-======================================================
                        prop_rot
=======================================================-}
 {-@ LIQUID "--no-totality" @-}
 {-@ inline prop_rot_p @-}
prop_rot_p c = c =*= (rotR  (rotL c))

{-@  prop_rot :: c:CList Int -> { prop_rot_p c  } @-}
prop_rot :: CList Int -> Proof
prop_rot c@Empty = c =*= (rotR  (rotL c))
                    ? (
                         (rotR  (rotL c))
                         ===  rotR  Empty
                         ===   Empty
                    )
                    ? lemma_refl (Empty::CList Int)
                  === c =*= Empty
                  ***QED 

                  
prop_rot c@(CList [] _ [])  = c =*= (rotR  (rotL c))
                                ? (
                                    (rotR  (rotL c))
                                    ===  rotR  c
                                    ===   c
                                )
                                ? lemma_refl c
                            === c =*= c
                            ***QED 

                            
prop_rot c@(CList (l:ls) f rs)  =  c =*= (rotR  (rotL c))
                            ?( (rotR (rotL c))
                            === (rotR (CList ls l (f:rs)))
                            === CList (l:ls) f rs
                            )
                            ? lemma_refl (CList (l:ls) f rs)
                            === c =*= CList (l:ls) f rs
                            ***QED  

prop_rot c@(CList [] f rs)  =  c =*= (rotR  (rotL c))
                            ? ((rotR (rotL c))
                            === (rotR (let (l:ls) = reverse rs
                                        in CList ls l [f]))
                            === (let (l:ls) = reverse rs
                                  in  rotR (CList ls l [f])
                                )
                            === (let (l:ls) = reverse rs
                                  in  (CList (l:ls) f [])
                                )
                            ===  (CList (reverse rs) f [])
                            )
                            === c =*= (CList (reverse rs) f [])
                            === (any ((toList c ==) . toList) . toList $ allRotations (CList (reverse rs) f [])) 
                            -- def of allRotations
                            === (let 
                                    lls = unfoldr (fmapLMaybe joinTuple . mRotL) (CList (reverse rs) f [])
                                    rrs = unfoldr (fmapLMaybe joinTuple . mRotR) (CList (reverse rs) f []) 
                                in (any ((toList c ==) . toList) . toList $ CList lls (CList (reverse rs) f []) rrs )
                                === (any ((toList c ==) . toList)  (toList (CList lls (CList (reverse rs) f []) rrs)))
                                === (any ((toList c ==) . toList)  (rightElements (CList lls (CList (reverse rs) f []) rrs)))
                                === (any ((toList c ==) . toList)  ((CList (reverse rs) f []): (rrs ++ reverse lls)))
                                    -- def of any
                                === ( ((toList c ==) . toList) (CList (reverse rs) f []) || (any ((toList c ==) . toList)  (rrs ++ reverse lls)))
                                    ? (
                                        ((toList c ==) . toList) (CList (reverse rs) f [])
                                    === (toList c == toList (CList (reverse rs) f []))
                                    === (rightElements c == rightElements (CList (reverse rs) f []))
                                    === (f :( rs ++ reverse []) == f : ([] ++(reverse (reverse rs))))
                                    === (f :( rs ++ []) == f : (reverse (reverse rs)))
                                        ? involutionP rs
                                        ? rightIdP rs
                                    === (f : rs == f : rs)
                                    )
                                === ( (f : rs == f : rs) || (any ((toList c ==) . toList)  (rrs ++ reverse lls)))
                                )
                            ***QED

