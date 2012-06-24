module T where

import Tests.KesterelBasis

-- Exception is thrown, so we terminate in the first instant.
e = catchE (\e0 -> (catchE $ \e1 -> throwE e0) >>> pauseE)
c = unitA >>> runE e

prop_correct = property (\xs -> simulate c xs == take (length xs) (zip (true : repeat false) (repeat ())))
test_constructive = isJust (isConstructive c)
