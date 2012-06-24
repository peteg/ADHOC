{-# LANGUAGE TypeFamilies #-}
{- In-Haskell truth table enumerator for combinational cyclic circuits.
 - Copyright   :  (C)opyright 2009 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -}
module ADHOC.TruthTable
    ( TTArrow
    , tt
    ) where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude hiding ( id, (.) )
import ADHOC.Circuits
import ADHOC.Simulate

-------------------------------------------------------------------
-- FIXME We need a QuickCheck-style generator story here.
-------------------------------------------------------------------

class Enumerable a where
    enumeration :: [a]

-- FIXME often we just care about defined inputs.
instance Enumerable SimBool where
--     enumeration = [minBound .. maxBound]
    enumeration = [false, true]

instance Enumerable () where enumeration = [()]
instance (Enumerable a, Enumerable b) => Enumerable (a, b) where
    enumeration = [ (a, b) | a <- enumeration, b <- enumeration ]
instance (Enumerable a, Enumerable b, Enumerable c) => Enumerable (a, b, c) where
    enumeration = [ (a, b, c) | a <- enumeration, b <- enumeration, c <- enumeration ]

-------------------------------------------------------------------
-- The simulator for cyclic combinational logic is 'SyncFun' in drag.
-------------------------------------------------------------------

newtype TTArrow (~>) b c = TTA (SyncFun BitView (~>) b c)
    deriving (Category, Arrow, ArrowLoop)

-- FIXME we can't derive ArrowComb because we need to specify our
-- boolean type. File a bug report?
instance Arrow (~>) => ArrowComb (TTArrow (~>)) where
    type B (TTArrow (~>)) = SimBool

    falseA = TTA falseA
    trueA = TTA trueA

    andA = TTA andA
    notA = TTA notA

instance (ArrowApply (~>), ArrowChoice (~>), Fix r, Eq r)
      => ArrowCombLoop (TTArrow (~>)) r where
    combLoop (TTA f) = TTA (combLoop f)

-- FIXME improve formatting.
tt :: (Enumerable b, Show b, Show c)
   => TTArrow (Kleisli IO) b c -> IO ()
tt (TTA f) =
    sequence_
      [ do [c] <- runKleisli (runSyncFun (arr snd >>> f)) ((), [b])
           putStrLn $ (shows b . showString " -> " . shows c) ""
        | b <- enumeration ]
