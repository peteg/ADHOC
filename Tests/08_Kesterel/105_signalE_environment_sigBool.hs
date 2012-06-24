-- Ensure the "right" environment gets returned.
module T where

import Tests.KesterelBasis

e = signalE $ \s ->
      proc () ->
        do (| loopE (do emitE s -< ()
                        pauseE  -< ()) |)
           sigE s -< ()

c = runE e

prop_correct = property (\xs ->
                         simulate c xs
                      == take (length xs) (zip (repeat false) (repeat true) ) )
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
