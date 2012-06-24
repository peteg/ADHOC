-- Check that sustain_while works.

module T where

import Tests.KesterelBasis
import Tests.ModelCheckerBasis

pid = "probe"

e0 = signalE $ \s ->
      probeSigE pid s >>> sustain_whileE s pauseE

Just (m0, _) = isConstructive (unitA >>> runE e0)
ctlM0 = mkCTLModel m0

test_pause = isOK (mc ctlM0 (probe pid /\ ax (ag (neg (probe pid)))))

--------------------

e1 = signalE $ \s ->
      probeSigE pid s >>> sustain_whileE s (pauseE >>> pauseE)

Just (m1, _) = isConstructive (unitA >>> runE e1)
ctlM1 = mkCTLModel m1

test_pause_pause = isOK (mc ctlM1 (probe pid /\ ax (probe pid /\ ax (ag (neg (probe pid))))))

--------------------

e2 = signalE $ \s ->
      probeSigE pid s >>> sustain_whileE s nothingE

Just (m2, _) = isConstructive (unitA >>> runE e2)
ctlM2 = mkCTLModel m2

test_nothing = isOK (mc ctlM2 (ag (neg (probe pid))))
