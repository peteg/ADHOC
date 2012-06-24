module T where

import Tests.KesterelBasis

-- Signal is not emitted but is tested, so there is no need to combLoop in signalE.
e = signalE $ \s -> proc x ->
  do (| (presentE s)
	     (pauseE -< x)
             (nothingE -< x) |)
     sigE s -< ()

c = idB >>> runE e

prop_correct = property (\xs -> let xs' = map unSimBoolDef xs in simulate c xs' == take (length xs) (zip (true : repeat false) (repeat false)))
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
