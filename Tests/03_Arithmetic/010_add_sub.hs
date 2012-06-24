module T where

import Tests.Basis
import ADHOC.Internals ( cbool2bdd )
import ADHOC.Data.Arithmetic

a g x y = unitA >>> (g <<< constNatA (undefined :: Four) x &&& constNatA (undefined :: Four) y)

c g x y z =
  proc () ->
    do s <- a g x y -< ()
       eqA <<< second (constNatA (undefined :: Four) z) -< (s, ())

f g x y z = cbool2bdd (snd (fromJust (isConstructive (c g x y z))))

prop_add_eq = property $ \x y ->
  if x >= 0 && y >= 0 && x < 16 && y < 16
     then f addA x y (xpy x y) == true
     else true
  where xpy x y = if x + y > 15 then 15 else x + y

prop_sub_eq = property $ \x y ->
  if x >= 0 && y >= 0 && x < 16 && y < 16
     then f subA x y (xsy x y) == true
     else true
  where xsy x y = if x - y < 0 then 0 else x - y
