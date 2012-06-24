-- Stripped down robot example.
module T where

import Tests.KesterelBasis

e = arr (\() -> ()) >>> (haltE |||| haltE) >>> (arr (const ()))
c = runE e

prop_correct = property (\xs -> simulate c xs == zip (repeat false) xs)
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
