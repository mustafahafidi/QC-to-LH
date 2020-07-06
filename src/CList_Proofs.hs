{- 
=================================================================
                      Data.CircularList proofs
    *With --no-adt this file is unsafe
    please see the new proofs (safe) in Test/CList_proofs done using `lhp`
=================================================================
-}


module CList_Proofs where
import Lib.LH.Prelude
-- import Lib.LH.Equational
import Lib.CL.CircularList hiding ((=*=))
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (length, null, splitAt, (++), reverse,any)

{-@ LIQUID "--reflection"    @-}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-totality"    @-}
{-@ LIQUID "--diff"    @-}
{-@ LIQUID "--no-adt"    @-}


{-@ reflect =*= @-}
{-@ infix 4 =*= @-}
(=*=) :: Eq a  => CList a -> CList a -> Bool
a =*= b = (any ((toList a ==) . toList) . toList $ allRotations b)
         -- (any (\x -> (toList a == toList x )) (toList (allRotations b)))
-- rewriting necessary because of https://github.com/ucsd-progsys/liquidhaskell/issues/1671 if you want to import (=*=) in other files


{-======================================================
                        prop_empty
=======================================================-}
{-@ prop_empty :: { length (toList empty) == 0} @-}
prop_empty :: Proof
prop_empty = length (toList empty) === 0
             ***QED 


{-======================================================
                        prop_isEmpty
=======================================================-}
{-@ prop_isEmpty :: l:[Int] -> { null l == isEmpty (fromList l)} @-}
prop_isEmpty :: [Int] -> Proof
prop_isEmpty l = null l === isEmpty (fromList l)
             ***QED 


{-======================================================
                        prop_size
=======================================================-}
{-@ prop_size :: l:[Int] -> { (length l) == (size (fromList l)) } @-}
prop_size :: [Int] -> Proof
prop_size l = (length l) === (size (fromList l))
             ***QED 
             
{-======================================================
                        prop_focus
=======================================================-}            
{-@ prop_focus :: c:CList Int -> v:Int -> {(Just v) == (focus (insertR v c))} @-}
prop_focus :: CList Int -> Int -> Proof
prop_focus c v = (Just v) === (focus $ insertR v c)
                  ***QED 


 
{- ===============  Additional props ====================-}
{-======================================================
                        prop_singleton
=======================================================-}
{-@ prop_singleton :: i:Int -> {toList (singleton i) == [i] && size (singleton i) == 1} @-}
prop_singleton :: Int -> Proof
prop_singleton i = ([i]
                    === i : ([])
                    === i : ([] ++ [])
                    === i : ([] ++ (reverse []))
                    === rightElements (CList [] i [])
                    === toList (CList [] i [])
                    === toList (singleton i) 
                    ***QED)  &&&
                   (size (singleton i) === 1
                   ***QED)


{-======================================================
                prop_fromList_focus
=======================================================-}
{-@ prop_fromList_focus ::  {focus (fromList ([1])) == Just 1} @-}
prop_fromList_focus ::  Proof
prop_fromList_focus = focus (fromList ([1]::[Int])) === Just 1
                                ***QED


{-======================================================
               prop_focus_update
=======================================================-}
{-@ prop_focus_update :: v:Int -> cl:CList Int -> 
                        { focus (update v cl) == Just v} 
@-}
prop_focus_update :: Int -> CList Int -> Proof
prop_focus_update v cl = focus (update v cl) === Just v
                          ***QED 


{-======================================================
              prop_reverse_direction
=======================================================-}
{-@ prop_reverse_direction ::  cl:CList Int -> 
                { reverseDirection (reverseDirection cl) == cl && 
                  size (reverseDirection cl) == size cl} @-}
prop_reverse_direction ::  CList Int -> Proof
prop_reverse_direction cl = (reverseDirection (reverseDirection cl) === cl
                            ***QED)
                            &&& (size (reverseDirection cl) === size cl
                            ***QED)
                          
{-======================================================
                       prop_insertR 
=======================================================-}
{-@ prop_insertR ::  i:Int -> cl:CList Int -> {size (insertR i cl) == size cl+1} @-}
prop_insertR ::  Int -> CList Int -> Proof
prop_insertR i cl = size (insertR i cl) === size cl+1
                          ***QED 



{-======================================================
                   prop_insertR_removeR     
=======================================================-}
{-@ prop_insertR_removeR ::  v:Int -> cl:CList Int -> {removeR (insertR v cl) == cl} @-}
prop_insertR_removeR ::  Int -> CList Int -> Proof
prop_insertR_removeR v cl = removeR (insertR v cl)
                          === (case cl of
                                Empty -> removeR (CList [] v [])
                                (CList l f r) -> removeR (CList l v (f:r)))
                        
                         === cl
                         ***QED


{-======================================================
                        prop_update
=======================================================-}
{-@ prop_update :: v:Int -> cl:CList Int -> 
                 { cl == Empty ==> size (update v cl) == 1 && 
                   cl != Empty ==> size (update v cl) == size cl } 
@-}
prop_update :: Int -> CList Int -> Proof
prop_update v cl@Empty = size (update v cl) 
                       === size (CList [] v [])
                       === 1
                       ***QED 
                         
prop_update v cl@(CList l _ r) = size (update v cl) 
                               === size (CList l v r) 
                               === size cl
                               ***QED 



{-======================================================
                       prop_removeR 
=======================================================-}
{-@ prop_removeR ::  cl:CList Int -> 
                { cl == Empty ==> size (removeR cl) == 0 &&
                  cl != Empty ==> size (removeR cl) == (size cl)-1 } @-}

prop_removeR ::  CList Int -> Proof
prop_removeR cl@Empty = size (removeR cl) === 0
                        ***QED 

prop_removeR cl@(CList [] _ []) =   size (removeR cl) 
                                ===   size (Empty)      
                                ===  (size cl)-1
                                ***QED

prop_removeR cl@(CList l _ (r:rs)) =  size (removeR cl) 
                                   ===   size (CList l r rs)      
                                   ===   (size cl)-1
                                   ***QED

prop_removeR  cl@(CList l _ []) = size (removeR cl)
                                === (let (f:rs)=reverse l in
                                     size(CList [] f rs)) 
                                ===  (size cl)-1
                                ***QED
 

 
{-======================================================
                        prop_list
=======================================================-}
{-@ inline prop_list_p@-}
prop_list_p c = c =*= (fromList . toList $ c)

{-@ prop_list :: c:CList Int -> { prop_list_p c } @-}
prop_list :: CList Int -> Proof
prop_list c@Empty = (c =*= (fromList . toList $ c))
                === (c =*= (fromList (toList c)))
                      ? (
                      (fromList (toList  c))
                      === (fromList (toList Empty))
                      === (fromList (rightElements Empty))
                      === (fromList [])
                      === Empty
                      )
                === (c =*= Empty)
                    ? lemma_refl c
                     ***QED

prop_list c@(CList l f r) = (c =*= (fromList . toList $ c))
                                            ? (
                                                (fromList (toList c))
                                                === (fromList (rightElements c))
                                                === (fromList (f : (r ++ (reverse l))))
                                            ) 
                        === (let 
                                a@(i:is) = f : (r ++ (reverse l))
                                len = length a
                                (sr,sl) = splitAt (len `div` 2) is
                                b = CList (reverse sl) i sr
                            in  c =*= b
                            
                            === (any ((toList c ==) . toList) . toList $ allRotations b)
                            === (let --def of allRotations
                                    ls = unfoldr (fmapLMaybe joinTuple . mRotL) b
                                    rs = unfoldr (fmapLMaybe joinTuple . mRotR) b
                                in (any ((toList c ==) . toList) . toList $ CList ls b rs)
                                                                ? (toList (CList ls b rs)
                                                                === rightElements (CList ls b rs)
                                                                === b : (rs ++ (reverse ls))
                                                                )
                                === (any ((toList c ==) . toList)  (b : (rs ++ (reverse ls))))
                                    -- def of any
                                === (let p = ((toList c ==) . toList) 
                                     in (p b || any p (rs ++ (reverse ls)))
                                        ? ( p b
                                        === ((toList c ==) . toList) (CList (reverse sl) i sr)
                                        === (toList c == toList (CList (reverse sl) i sr))
                                        === (rightElements c == rightElements (CList (reverse sl) i sr))
                                        === ((f : (r ++ (reverse l))) == (i : (sr ++ (reverse (reverse sl)))))
                                                                        ? (
                                                                            (i : (sr ++ (reverse (reverse sl))))
                                                                                        ? involutionP sl
                                                                        === (f : (sr ++ sl))
                                                                            ? splitAt_theorem (len `div` 2) is
                                                                        === (f : is)
                                                                        === (f : (r ++ (reverse l)))
                                                                        )
                                        )
                                    )
                                )
                            )
                            ***QED

{-======================================================
                        prop_rot
=======================================================-}
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



{-======================================================
                        prop_packL
=======================================================-}
{-@ inline prop_packL_p @-}
prop_packL_p c = c =*= (packL c)
{-@ prop_packL ::  c:CList Int -> { prop_packL_p c } @-}
prop_packL ::  CList Int -> Proof
prop_packL c@Empty =   c =*= (packL c)
                  ===  c =*= (Empty)
                     ? lemma_refl c
                       ***QED

prop_packL c@(CList l f r) = c =*= (packL c)
                            === c =*= (packL c)
                            === c =*= (CList (l ++ (reverse r)) f [])
                            === (any ((toList c ==) . toList) . toList $ allRotations (CList (l ++ (reverse r)) f []))
                            === (any ((toList c ==) . toList) . toList $ (allRotations (CList (l ++ (reverse r)) f [])))
                            === (
                                let 
                                    cl = (CList (l ++ (reverse r)) f [])
                                    ls = unfoldr (fmapLMaybe joinTuple . mRotL) cl
                                    rs = unfoldr (fmapLMaybe joinTuple . mRotR) cl
                                in (any ((toList c ==) . toList) . toList $  (CList ls cl rs))
                                    === (any ((toList c ==) . toList)  (toList (CList ls cl rs)))
                                                                  ?(toList (CList ls cl rs)
                                                                    === rightElements  (CList ls cl rs)
                                                                    === cl : (rs ++ (reverse ls)))
                                    === (any ((toList c ==) . toList) (cl : (rs ++ (reverse ls))))
                                    === let p = (toList c ==) . toList in 
                                         (((toList c ==) . toList) cl || any p (rs ++ (reverse ls)))
                                         ? (
                                             ((toList c ==) . toList) cl
                                        ===  (toList c == toList cl)
                                        ===  (rightElements c == rightElements cl)
                                        ===  (f : (r ++ (reverse l)) == f : ([] ++ (reverse (l++(reverse r)))))
                                                                           ?(([] ++ (reverse (l++(reverse r))))
                                                                           === (reverse (l ++ (reverse r)))
                                                                                ? (distributivityP l (reverse r))
                                                                           === ((reverse (reverse r)) ++ (reverse l))
                                                                                ? involutionP r
                                                                           === ( r ++ (reverse l))
                                                                           )
                                         )
                                )
                            ***QED


{-======================================================
                        prop_packR
=======================================================-}
{-@ inline prop_packR_p @-}
prop_packR_p c = c =*= (packR c)
{-@ prop_packR ::  c:CList Int -> { prop_packR_p c } @-}
prop_packR ::  CList Int -> Proof
prop_packR c@Empty =  c =*= (packR c)
                  === c =*= Empty
                    ? lemma_refl c
                       ***QED 

prop_packR c@(CList l f r) = c =*= (packR c)
                            === c =*= CList [] f (r ++ (reverse l))
                            === (let cl = CList [] f (r ++ (reverse l)) in
                                (any ((toList c ==) . toList) . toList $ allRotations cl)
                            === ( let --def of allRotations
                                    ls = unfoldr (fmapLMaybe joinTuple . mRotL) cl
                                    rs = unfoldr (fmapLMaybe joinTuple . mRotR) cl
                                in (any ((toList c ==) . toList) . toList $ CList ls cl rs)
                                                                 ? (toList (CList ls cl rs)
                                                                    === rightElements (CList ls cl rs)
                                                                    === cl : (rs ++ (reverse ls))
                                                                  )
                                === ( any ((toList c ==) . toList) (cl : (rs ++ (reverse ls))) )
                                === ( ((toList c ==) . toList) cl || any ((toList c ==) . toList)  (rs ++ (reverse ls)) )
                                    ? (((toList c ==) . toList) cl
                                    === (toList c == toList cl)
                                    === (rightElements c == rightElements cl)
                                    === (f : (r ++ (reverse l)) == f : ((r ++ (reverse l)) ++ (reverse [])))
                                                                        ? ( ((r ++ (reverse l)) ++ (reverse []))
                                                                        ===  ((r ++ (reverse l)) ++  [])
                                                                            ? rightIdP (r ++ (reverse l))
                                                                        ===  (r ++ (reverse l))
                                                                        )
                                    )
                                )
                            )
                            ***QED



{-===================================================================================
                         START Theorems
=====================================================================================-}
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

 