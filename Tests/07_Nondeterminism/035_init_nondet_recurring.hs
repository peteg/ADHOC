module T where

import Prelude hiding ( id )
import Tests.ModelCheckerBasis

-- Some initial states. Choose new states in the next instant when the
-- first of the pair is true.
c = proc () ->
  do rec x <- (| unsafeNonDetAC (\x -> xorA -< x) (arr fst -< x) |)
     returnA -< x

Just (m, (a, b)) = isConstructive c
ctlM = mkCTLModel m

test_model = ctlM `seq` True
test_nondet_inv = isOK (mc ctlM (ag (prop a `xor` prop b)))
test_nondet_rec_no_change = isOK (mc ctlM (ag (neg (prop a) --> ax (neg (prop a)))))
test_nondet_rec_change = isOK (mc ctlM (ag (prop a --> (ex (neg (prop a)) /\ ex (prop a)))))
