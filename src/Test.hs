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
-- {-@ LIQUID "--exactdc"    @-}






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


{-@ inline refl @-}
refl cl = cl =*= cl

{-@ lemma_refl ::  Eq a => cl:CList a -> { refl cl} @-}
lemma_refl :: Eq a =>  CList a -> Proof
lemma_refl Empty = p3_proof
lemma_refl cl@(CList l f r) = refl cl 
                           === cl =*= cl
                           === ( any ((toList cl ==) . toList) . toList $ allRotations cl) -- def. allRotations
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



{-@ mRotR :: cl:CList a -> LMaybe { cr: (CList a) | cl } @-}

{-======================================================
                        proving p1
=======================================================-}
{-@ p1_proof ::  {p1} @-}
p1_proof ::  Proof
p1_proof =  CList [] 0 [1] =*= CList [1] 0 []
        === ( any ((toList (CList [] 0 [1]) ==) . toList) . toList $ allRotations (CList [1] 0 []) )
                -- def of allRotations
        === ( let  ls =  unfoldr (fmapLMaybe joinTuple . mRotL) (CList [1] 0 [])
                          ?(      (fmapLMaybe joinTuple . mRotL) (CList [1] 0 [])
                                ===  fmapLMaybe joinTuple  (mRotL (CList [1] 0 []))
                                ===  fmapLMaybe joinTuple  (LJust (CList [] 1 [0]))
                                ===  LJust( joinTuple  (CList [] 1 [0]) ) 
                                ===  LJust (CList [] 1 [0],CList [] 1 [0])
                                ***QED)
                        === (CList [] 1 [0]) : (unfoldr f (CList [] 1 [0]))
                   rs =  unfoldr (fmapLMaybe joinTuple . mRotR) (CList [1] 0 [])

              in  ( 
                      (\ls -> any ((toList (CList [] 0 [1]) ==) . toList) (toList ls)) $ CList ls (CList [1] 0 []) rs 
              )
        --       === (  any ((toList (CList [] 0 [1]) ==) . toList) (toList (CList ls (CList [1] 0 []) rs)) ) 
        --       === (  any ((toList (CList [] 0 [1]) ==) . toList) (rightElements (CList ls (CList [1] 0 []) rs)) ) 
        --         -- def of any
        --       === ( let p = ((toList (CList [] 0 [1]) ==) . toList)
        --                 (x:xs) = ((CList [1] 0 []) : (rs ++ (reverse ls)))
        --         in  (p x || any p xs )
        --         === ((toList (CList [] 0 [1]) == toList (CList [1] 0 []) || any p xs ))
        --         )
        --       === (  any ((toList (CList [] 0 [1]) ==) . toList) (toList (CList ls (CList [1] 0 []) rs)) ) 
            )
        -- === ( any ((toList (CList [] 0 [1]) ==) . toList) . toList $ allRotations (CList [1] 0 []) )
        -- === CList [] 0 [1] =*= CList [1] 0 []
        ***Admit
        

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


