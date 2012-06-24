module T where

import Prelude ()
import Tests.Basis
import ADHOC.Internals ( cbool2bdd )
import ADHOC.Data.Arithmetic

a x y = unitA >>> (eqA <<< constNatA (undefined :: Four) x &&& constNatA (undefined :: Four) y)
f x y = cbool2bdd (snd (fromJust (isConstructive (a x y))))

-- FIXME QuickCheck's ==> gives up too readily (the generator uses massive numbers).
-- Probably want exhaustive checking here, not random.
prop_eq = property $ \x y ->
  if x >= 0 && y >= 0 && x < 16 && y < 16
     then f x y == (if x == y then true else false)
     else true

-- FIXME these tests are borked due to a lack of strictness in constNat4. Might be hard to get right.
exception_neg = isConstructive (unitA >>> constNatA (undefined :: Four) (-1))
exception_overflow = isConstructive (unitA >>> constNatA (undefined :: Four) 16)
