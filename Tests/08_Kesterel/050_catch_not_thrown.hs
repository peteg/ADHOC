module T where

import Tests.KesterelBasis

-- Exception is not thrown.
e = catchE $ \_exn -> nothingE
c = unitA >>> runE e

prop_correct = property (\xs -> simulate c xs == zip (true : repeat false) xs)
test_constructive = isJust (isConstructive c)
