module T where

import Tests.KesterelBasis

e = signalE $ \(s1 :: Signal, s2) -> emitE s2

c = idB >>> runE e

test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
