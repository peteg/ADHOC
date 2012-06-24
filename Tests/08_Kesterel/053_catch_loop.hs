module T where

import Tests.KesterelBasis

-- Terminate in the first instant.

-- This is not loop-safe, and the circuit translation is non-constructive.
-- e = loopE_ $ \e -> throwE e
e = loopE_ $ \e -> throwE e >>> pauseE
c = unitA >>> runE e

prop_correct = property (\xs -> simulate c xs
                             == take (length xs) (zip (true : repeat false) (repeat ())))

test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
