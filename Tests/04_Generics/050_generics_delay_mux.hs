-- delay and mux a tuple of bits.

module T where

import Tests.Basis

c = proc () ->
  do rec x <- (| delayAC (trueA &&& falseA -< ()) (returnA -< swapA x) |)
     (| muxAC (returnA -< fst x) (returnA -< snd x) (returnA -< fst x) |)

prop_correct = property (\xs -> simulate c xs == replicate (length xs) false)
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
