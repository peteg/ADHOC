-- show that probes work.
module T where

import Tests.ModelCheckerBasis

c = proc () ->
      (| combLoop (\x ->
           do y <- (| delayAC (trueA -< ()) (returnA -< x) |)
              probeA "y" -< y
              dupA <<< notA -< y ) |)

Just (m, out) = isConstructive c
ctlM = mkCTLModel m

test_mc_out = isOK (mc ctlM (ag (prop out <-> ax (neg (prop out)))))
test_mc_probe = isOK (mc ctlM (ag (probe "y" <-> neg (prop out))))
test_mc_probe_not = not (isOK (mc ctlM (ag (probe "y" <-> prop out))))
