-- Ensure the "right" environment gets returned.
module T where

import Tests.KesterelBasis

e = signalE $ \s ->
      proc () ->
        do x <- (| loopE (do emitE s -< ()
                             sigE s <<< pauseE -< () ) |)
           returnA -< x

c = runE e

prop_correct = property (\xs ->
                         simulate c xs
                      == take (length xs) (zip (repeat false) (repeat true) ) )
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
