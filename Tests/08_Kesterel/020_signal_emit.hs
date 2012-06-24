module T where

import Tests.KesterelBasis

e = signalE $ \s ->
      proc x -> (| loopE (do emitE s -< ()
                             pauseE -< x) |)
c = arr (\() -> ()) >>> runE e

Just (m, (terminated, ())) = isConstructive c
ctlM = mkCTLModel m

ok_constructive = m
ok_netlist = runNL c

prop_correct = property (\xs -> simulate c xs == zip (repeat false) xs)
test_mc_terminated = isOK (mc ctlM (ag (neg (prop terminated))))
