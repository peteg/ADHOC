-- delay a tuple of bits.

module T where

import Tests.Basis

c = proc () ->
  do rec x <- (| delayAC (trueA &&& falseA -< ()) (returnA -< x) |)
     returnA -< x

prop_correct = property (\xs -> simulate c xs == replicate (length xs) (true, false))
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
