module T where

import Tests.KesterelBasis

-- The identity on booleans.
e = signalE $ \s -> proc x ->
      (| loopE (do x <- (| ifE (returnA -< x) (emitE s -< ()) (nothingE -< ()) |)
                   pauseE -< ()
                   sigE s -< ()) |)

c = runE e

prop_correct = property (\xs -> let xs' = map unSimBoolDef xs in simulate c xs' == zip (repeat false) xs')
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
