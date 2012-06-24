module T where

import Tests.KesterelBasis

e = signalE $ \s0 ->
      signalE $ \s1 ->
        (loopE $   ((pauseE >>> emitE s1) `abortE` s0
             |||| (pauseE >>> emitE s0))
          >>> pauseE) >>> sigE s1

c = unitA >>> runE e

prop_correct = property (\xs -> simulate c xs == replicate (length xs) (false, false))
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
