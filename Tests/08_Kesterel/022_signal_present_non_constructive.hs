module T where

import Tests.KesterelBasis

-- Information flows backwards, so it's not constructive.
e = signalE $ \s ->
      (presentE s
 	pauseE
	nothingE)
      >>> emitE s

c = unitA >>> runE e

prop_correct = property (\xs -> simulate c xs == zip (bottom : bottom : repeat false) xs)
test_constructive = isNothing (isConstructive c)
ok_netlist = runNL c
