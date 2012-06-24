-- delay and mux a tuple of numbers.

module T where

import Tests.Basis
import ADHOC.Data.Arithmetic

c = proc () ->
  do rec x <- (| delayAC (constNatA (undefined :: Four) 2 &&& constNatA (undefined :: Four) 5 -< ()) (returnA -< swapA x) |)
         y <- (| delayAC (falseA -< ()) (notA -< y) |)
     (| muxAC (returnA -< y) (returnA -< snd x) (returnA -< fst x) |)

prop_correct = property (\xs -> simulate c xs == replicate (length xs) 2)
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
