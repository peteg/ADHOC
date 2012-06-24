module T where

import Tests.KesterelBasis

-- FIXME not so hot
e = signalE $ \s -> (emitE s |||| nothingE) >>> sigE s
c = unitA >>> runE e

prop_correct = property (\xs -> simulate c xs
                     == take (length xs) (zip (true : repeat false) (true : repeat false)))
test_constructive = isJust (isConstructive c)
