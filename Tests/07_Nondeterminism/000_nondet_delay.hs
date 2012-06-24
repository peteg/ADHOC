module T where

import Tests.ModelCheckerBasis

c = unitA >>> delayAC trueA (nondetAC falseA trueA)

Just (m, out) = isConstructive c
ctlM = mkCTLModel m

test_model_ok = ctlM `seq` True
test_nondet_ag_ef_out = isOK (mc ctlM (ag (ef (prop out))))
test_nondet_ag_ef_neg_out = isOK (mc ctlM (ag (ef (neg (prop out)))))
test_nondet_not_ag_out = isOK (mc ctlM (ag (prop out))) == False
test_nondet_not_ag_neg_out = isOK (mc ctlM (ag (neg (prop out)))) == False
