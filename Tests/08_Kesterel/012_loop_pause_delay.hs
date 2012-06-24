module T where

import Tests.KesterelBasis

-- Initially falseA then the input delayed by one cycle.
e = proc env -> (| loopE (do pauseE -< ()
                             lift (delayAC falseA returnA) -< env) |)
c = runE e

prop_correct = property (\xs -> take (length xs) (simulate c xs)
                             == take (length xs) (zip (repeat false) (false : xs)))

test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
