module T where

import Tests.KesterelBasis

e = signalE $ \(s1, s2 :: Signal) -> emitE s1

c = idB >>> runE e

test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
