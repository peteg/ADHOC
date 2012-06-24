module T where

import Tests.Basis
import ADHOC.Internals ( cbool2bdd )
import ADHOC.Data.Arithmetic

-- Quick or scalable test...
-- type Width = Fourteen
type Width = Four

a g x y = unitA >>> (g <<< constNatA (undefined :: Width) x &&& constNatA (undefined :: Width) y)

c g x y z =
  proc () ->
    do s <- a g x y -< ()
       eqA <<< second (constNatA (undefined :: CardAdd Width Width) z) -< (s, ())

f g x y z = cbool2bdd (snd (fromJust (isConstructive (c g x y z))))

prop_mul_eq = property $ \x y ->
  let x' = abs x
      y' = abs y
  in if x' < limit && y' < limit
       then -- trace ("testing: " ++ show x' ++ " * " ++ show y') $
              f mulA x' y' (xpy x' y') == true
       else -- trace ("skipping: " ++ show x ++ " * " ++ show y) $
              true
  where
    xpy x y = x * y
    limit = 2 ^ (c2num (undefined :: Width) :: Integer)
