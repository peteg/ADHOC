module T where

import Tests.KesterelBasis

-- A local signal, not emitted.

e = signalE $ \(s::Signal) -> loopE pauseE
c = unitA >>> runE e

prop_correct = property (\xs -> simulate c xs == zip (repeat false) xs)
test_constructive = isJust (isConstructive c)
