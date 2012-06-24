-- Tracking down a constructivity model-building bug.
module T where

import Tests.ModelCheckerBasis

c = combLoop (dupA <<< notA <<< delayAC (arr (const ()) >>> (trueA)) (arr (\((), x) -> x)))

Just (m, out) = isConstructive c
ctlM = mkCTLModel m

test_mc_out = isOK (mc ctlM (ag (prop out <-> ax (neg (prop out)))))
