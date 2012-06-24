module T where

import Tests.Basis
import ADHOC.Internals ( cbool2bdd )
import ADHOC.Data.Arithmetic

a g x y = unitA >>> (g <<< constNatA (undefined :: Four) x &&& constNatA (undefined :: Four) y)
f g x y = cbool2bdd (snd (fromJust (isConstructive (a g x y))))

prop_gt = property $ \x y ->
  if x >= 0 && y >= 0 && x < 16 && y < 16
     then f gtA x y == (if x > y then true else false)
     else true

prop_ge = property $ \x y ->
  if x >= 0 && y >= 0 && x < 16 && y < 16
     then f geA x y == (if x >= y then true else false)
     else true

prop_lt = property $ \x y ->
  if x >= 0 && y >= 0 && x < 16 && y < 16
     then f ltA x y == (if x < y then true else false)
     else true

prop_le = property $ \x y ->
  if x >= 0 && y >= 0 && x < 16 && y < 16
     then f leA x y == (if x <= y then true else false)
     else true
