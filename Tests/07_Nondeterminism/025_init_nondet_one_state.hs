module T where

import Prelude hiding ( id )
import Tests.ModelCheckerBasis

-- One initial state.
c = proc () ->
  do rec x <- (| unsafeNonDetAC (\x -> notA -< x) (idB -< x) |)
     returnA -< x

Just (m, out) = isConstructive c
ctlM = mkCTLModel m

test_model = ctlM `seq` True
test_nondet_init = isOK (mc ctlM (neg (prop out)))
