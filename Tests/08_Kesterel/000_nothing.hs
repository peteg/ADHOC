module T where

import Tests.KesterelBasis

-- e :: ArrowComb (~>) => E (~>) (B (~>)) ()
e = nothingE
c = unitA >>> runE e

-- prop_correct = property (\(xs :: [SimBool]) -> simulate c xs == zip (true : repeat false) xs)
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
