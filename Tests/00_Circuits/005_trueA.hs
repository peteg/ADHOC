-- The constant true circuit works.

module T where

import Tests.Basis

c = arr (\() -> ()) >>> trueA

prop_correct = property (\xs -> simulate c xs == take (length xs) (repeat true))
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
