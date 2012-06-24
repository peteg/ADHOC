-- A Lustre-like followed-by operator.
-- Should work in all constructive contexts.

module T where

import Tests.Basis

-- Note the use of idB here, for convenience.
c = proc i ->
     (| combLoop (\x ->
          do y <- (returnA -< x) `fby` (idB -< i)
             returnA -< (y, x)
                 ) |)

prop_correct = property (\xs -> simulate c xs == take (length xs) (bottom : tail xs))
test_constructive = isNothing (isConstructive c)

-- FIXME loops, due to combLoop being unfounded. Should be robust to this...
-- ok_netlist = runNL c
