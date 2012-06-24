module T where

import Prelude hiding ( id )
import ADHOC.Data.Arithmetic
import Tests.ModelCheckerBasis

c = proc () ->
  do rec x <- (| unsafeNonDetAC (\x -> leA <<< id &&& fromIntegerA 3 -< x) (falseA -< x) |)
     natA (undefined :: Four) -< x
     gtA <<< fromIntegerA 4 &&& id -< x

Just (m, out) = isConstructive c
ctlM = mkCTLModel m

test_model_ok = ctlM `seq` True
test_nondet_ag_out = isOK (mc ctlM (ag (prop out)))
test_nondet_not_ef_not_out = isOK (mc ctlM (ef (neg (prop out)))) == False
