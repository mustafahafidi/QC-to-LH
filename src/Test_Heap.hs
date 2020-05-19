
module Test_Heap where

import Lib.QC.Heap --(merge, Heap(..), (==?), toList)
import Lib.LH.Prelude
import Heap_Proofs
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (length, 
                        (++), 
                        reverse, 
                        iterate, 
                        null, 
                        splitAt,
                        any,
                        id,
                        minimum,
                        Maybe (..)
                        )

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--short-names" @-}
-- {-@ LIQUID "--diff"        @-}
-- {-@ LIQUID "--notermination" @-} 
