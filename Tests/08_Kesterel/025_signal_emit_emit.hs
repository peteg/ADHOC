module T where

import Tests.KesterelBasis

-- Emit a signal twice.
e = signalE $ \s ->
      proc x ->
        do emitE s -< ()
           emitE s -< ()
           returnA -< x

c = idB >>> runE e

prop_correct = property (\xs -> simulate c xs == zip (true : repeat false) xs)
test_constructive = isJust (isConstructive c)
