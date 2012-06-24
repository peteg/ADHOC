module T where

import Tests.KesterelBasis

-- Berry p130, parallel schizophrenia.
sustainE' s = loopE (emitE s >>> (nothingE |||| pauseE))

e sustain = unitA >>>
    (signalE $ \s ->
       (sustain s) |||| pauseE)

c = runE (e sustainE)
c' = runE (e sustainE')

prop_correct = property (\xs -> simulate c xs == simulate c' xs)
test_constructive0 = isJust (isConstructive c)
test_constructive1 = isNothing (isConstructive c')
ok_netlist0 = runNL c
ok_netlist1 = runNL c'
