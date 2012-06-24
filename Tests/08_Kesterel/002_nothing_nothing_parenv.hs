module T where

import Tests.KesterelBasis

-- e :: ArrowComb (~>) => E (~>) ((), ()) ((), ())
e = nothingE *** nothingE
c = arr (\((), ()) -> ((), ())) >>> runE e

prop_correct = property (\xs -> simulate c xs == zip (true : repeat false) xs)
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
