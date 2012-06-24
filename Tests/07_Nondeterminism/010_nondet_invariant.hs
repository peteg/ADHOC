module T where

import Prelude hiding ( id )
import Tests.ModelCheckerBasis

-- This is just trueA
c = proc () ->
  do rec x <- (| unsafeNonDetAC (\x -> returnA -< x) (falseA -< ()) |)
     returnA -< x

Just (m, out) = isConstructive c
ctlM = mkCTLModel m

test_model_ok = ctlM `seq` True
test_nondet_ag_out = isOK (mc ctlM (ag (prop out)))
test_nondet_not_ef_not_out = isOK (mc ctlM (ef (neg (prop out)))) == False
