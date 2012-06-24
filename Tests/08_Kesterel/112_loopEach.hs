-- Does loop_eachE work?
module T where

import Prelude ()
import Tests.KesterelBasis

-- c = unitA *** id >>> runE (bool2sig $ \r -> loopEachE r nothingE)
-- c = unitA *** id >>> runE (bool2sig $ \r -> loopE (abortE r haltE))
-- c = unitA >>> runE (signalE $ \r -> abortE r haltE)
c = unitA >>> runE (signalE $ \r -> loopE pauseE `abortE` r)

ok_netlist = runNL c
prop_correct = property (\xs -> simulate c xs == replicate (length xs) (false, ()))
test_constructive = isJust (isConstructive c)
