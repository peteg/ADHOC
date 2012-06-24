-- Constantly true.
module T where

import Tests.ModelCheckerBasis

c = unitA >>> delayAC trueA trueA

Just (m, out) = isConstructive c
ctlM = mkCTLModel m

ok_model = ctlM

test_out = isOK (mc ctlM (prop out))
test_neg_out = isOK (mc ctlM (neg (prop out))) == False
test_ex_out = isOK (mc ctlM (ex (prop out)))
test_ex_neg_out = isOK (mc ctlM (ex (neg (prop out)))) == False

test_eg_out = isOK (mc ctlM (eg (prop out)))
test_eg_neg_out = isOK (mc ctlM (eg (neg (prop out)))) == False

test_eu_out = isOK (mc ctlM (eu (prop out) true))
test_eu_neg_out = isOK (mc ctlM (eu (neg (prop out)) true))
