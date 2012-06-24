-- FIXME: This is not constructive, specifically in the second instant.
-- The presentE test in sigE depends on the later emitE microstep.

-- Now it is constructive as sigE means "give me the wire".

module T where

import Tests.KesterelBasis

e = signalE $ \s ->
      proc () ->
        do x <- (| loopE (do emitE s -< ()
                             pauseE  -< ()
                             sigE s -< ()) |)
           returnA -< x

c = runE e

prop_correct = property (\xs ->
                         simulate c xs
                      == take (length xs) (zip (repeat false) (true : repeat {-bottom-}true) ) )
test_constructive = {-isNothing-} isJust (isConstructive c)
ok_netlist = runNL c
