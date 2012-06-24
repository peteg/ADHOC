module T where

import Tests.ModelCheckerBasis

c =
  proc () ->
    (| combLoop (\x ->
         do a <- (| nondetAC (falseA -< ()) (returnA -< x) |)
            x' <- (| delayAC (trueA -< ()) (returnA -< a) |)
            returnA -< (x', x') ) |)

ok_netlist = runNL c
Just (m, out) = isConstructive c
ctlM = mkCTLModel m

test_model_ok = ctlM `seq` True

test_nondet_ag_ef_ag_neg_out = isOK (mc ctlM (ag (ef (ag (neg (prop out))))))
test_nondet_ag_ef_neg_out = isOK (mc ctlM (ag (ef (neg (prop out)))))
test_nondet_not_ag_out = isOK (mc ctlM (ag (prop out))) == False
test_nondet_not_ag_neg_out = isOK (mc ctlM (ag (neg (prop out)))) == False
