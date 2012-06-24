module T where

import Tests.KesterelBasis

-- Instantaneously termianting loop body.
e = arr (\() -> ()) >>> loopE nothingE
c = runE e

prop_correct = property (\xs -> simulate c xs
                             == zip (repeat false) xs)
ok_constructive = isNothing (isConstructive c)
ok_netlist = runNL c
