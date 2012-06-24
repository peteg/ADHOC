-- Berry, CONSTRUCTIVE SEMANTICS OF PURE ESTEREL, p130.

module T where

import Tests.KesterelBasis

-- Kernel expansion of "sustain s"

e =
  signalE $ \s ->
    proc env ->
      (| loopE (do emitE s -< ()
                   pauseE -< ())
       |)

c = unitA >>> runE e

prop_correct = property (\xs -> simulate c xs == replicate (length xs) (false, ()))
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
