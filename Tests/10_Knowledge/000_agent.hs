-- Check the agent construct is semantically neutral.
-- A circuit that is constructive in all states.

module T where

import Tests.KBPBasis

c = agent "neutral" $ proc () ->
  do boot <- delayAC falseA falseA -< ()
     combLoop (dupA <<< notA <<< andA) -< boot

test_constructive = isJust (isConstructive c)
