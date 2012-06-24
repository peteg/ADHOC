module T where

import Tests.KesterelBasis

e = loopE ((signalE $ \s -> (emitE s |||| nothingE) >>> sigE s) >>> dupA >>> first pauseE)
      >>> arr snd
c = unitA >>> runE e

prop_correct = property (\xs -> simulate c xs
                    == take (length xs) (zip (repeat false) (repeat true)) )
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
