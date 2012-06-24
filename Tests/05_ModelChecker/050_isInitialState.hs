-- Check the isInitialState combinator works.

module T where

import Tests.ModelCheckerBasis

c = arr (\() -> ()) >>> isInitialState

prop_correct = property (\xs -> simulate c xs == take (length xs) (true : repeat false))

-- The model checker requires states, i.e. delays.
c' = proc () ->
       do delayAC falseA falseA -< ()
          isInitialState -< ()

Just (m, isInitial) = isConstructive c'
ctlM = mkCTLModel m

test_mc_out = isOK (mc ctlM (prop isInitial /\ ax (ag (neg (prop isInitial)))))
