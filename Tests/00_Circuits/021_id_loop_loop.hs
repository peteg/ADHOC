-- id using harmless nested loops.

module T where

import Tests.Basis

c :: (ArrowComb (~>), ArrowLoop (~>)) => B (~>) ~> B (~>)
c = loop (swapA >>> first (loop swapA))

prop_correct = property (\x -> simulate c [x] == [x])
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
