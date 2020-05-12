import Language.Haskell.Liquid.ProofCombinators
import Lib.CL.CircularList
import Prelude hiding (any)
{-@ LIQUID "--reflection" @-}

{-@ reflect bar @-}
bar Empty = Empty
bar r@(CList [] _ []) = r
bar (CList (l:ls) f rs) = CList ls l (f:rs)
bar (CList [] f rs) = let (l:ls) = reverse rs
                       in CList ls l [f]
