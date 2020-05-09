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
{-@ LIQUID "--higherorder"    @-}
-- {-@ LIQUID "--short-names"    @-}



{-@ reflect =*= @-}
{-@ infix 4 =*= @-}
(=*=) :: Eq a  => CList a -> CList a -> Bool
a =*= b =  any ((toList a ==) . toList) . toList $ allRotations b


{-@ inline p1 @-}
p1 = (CList [] 0 [1] =*= CList [1] 0 [])

{-@ inline p2 @-}
p2  = (CList [] 0 [] =*= CList [] 0 [])

{-@ inline p3 @-}
p3  = (Empty =*= (Empty::CList Int))


{-======================================================
                        proving p2
=======================================================-}
{-@ p2_proof ::  {p2} @-}
p2_proof ::  Proof
p2_proof = p2
        === (CList [] 0 [] =*= CList [] 0 [])
        === ( any ((toList (CList [] 0 []) ==) . toList) . toList $ allRotations (CList [] 0 []) )
        
        ***Admit


{-======================================================
                        proving p3
=======================================================-}
{-@ p3_proof ::  { p3 } @-}
p3_proof ::  Proof
p3_proof = p3
        === Empty =*= (Empty::CList Int)
        === ( any ((toList Empty ==) . toList) . toList $ allRotations (Empty::CList Int) )
        === ( (\ls -> any ((toList Empty ==) . toList) (toList ls)) $ allRotations (Empty::CList Int) )
        === ( (\ls -> any ((toList Empty ==) . toList) (toList ls)) (allRotations (Empty::CList Int)) )
        === ( any ((toList Empty ==) . toList) (toList (allRotations (Empty::CList Int))) )
                                                      --  ?( allRotations (Empty)
                                                      --   === singleton (emptyB)
                                                      --   )

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


{-@ inline refl @-}
refl cl = cl =*= cl
{-@ lemma_refl ::  Eq a => cl:CList a -> { refl cl} @-}
lemma_refl :: Eq a =>  CList a -> Proof
lemma_refl Empty = p3_proof
lemma_refl cl@(CList l f r) = refl cl 
                           === cl =*= cl
                           === ( any ((toList cl ==) . toList) . toList $ allRotations cl) -- def. allRotations
                           === ( let  ls = unfoldr (\x->(fmapLMaybe (join(,))) (mRotL x)) cl

                                      rs = unfoldr (\x->(fmapLMaybe (join(,))) (mRotR x)) cl

                                 in     ( (\ls -> any ((toList cl ==) . toList) (toList ls)) $ CList ls cl rs )
                                    === ( any ((toList cl ==) . toList) (toList (CList ls cl rs)) )
                                    === ( any ((toList cl ==) . toList) (rightElements (CList ls cl rs)) )
                                          ? ( (\x-> toList cl == toList x) 
                                          === (\x-> (toList cl ==) (toList x))
                                          === ((toList cl ==) . toList)
                                            )
                                    === ( any (\x-> toList cl == toList x) (cl : (rs ++ (reverse ls))) )
                               )
                           ***Admit

