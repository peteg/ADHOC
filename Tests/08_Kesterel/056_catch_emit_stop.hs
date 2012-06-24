module T where

import Tests.KesterelBasis

-- Exception is thrown, so we don't emit anything.
e = signalE $ \s -> catchE $ \e -> throwE e >>> emitE s >>> sigE s
c = idB >>> runE e

prop_correct = property (\xs -> simulate c xs == take (length xs) (zip (true : repeat false) (repeat false)))
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
