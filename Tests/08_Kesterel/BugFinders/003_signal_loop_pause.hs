-- Tracking down a constructivity model-building bug.
module T where

import Tests.KesterelBasis

e = signalE (\(_::Signal) -> (loopE pauseE))
c = unitA >>> runE e

Just (m, (terminated, ())) = isConstructive c
ctlM = mkCTLModel m

ok_netlist = runNL c
test_mc_terminated = isOK (mc ctlM (ag (neg (prop terminated))))
