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
p1 = (CList [] 0 [1] =*= CList [1] 0 [])

{-@ inline p2 @-}
p2  = (CList [] 0 [] =*= CList [] 0 [])

{-@ inline p3 @-}
p3  = (Empty =*= (Empty::CList Int))



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
                                                       ?( allRotations (Empty)
                                                        === singleton (Empty)
                                                        )

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
