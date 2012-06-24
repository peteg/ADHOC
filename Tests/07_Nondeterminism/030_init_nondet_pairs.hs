module T where

import Prelude hiding ( id )
import Tests.ModelCheckerBasis

-- Some initial states.
c = proc () ->
  do rec x <- (| unsafeNonDetAC (\x -> xorA -< x) (falseA -< ()) |)
     returnA -< x

Just (m, (a, b)) = isConstructive c
ctlM = mkCTLModel m

test_model = ctlM `seq` True
test_nondet_init = isOK (mc ctlM (prop a `xor` prop b))
