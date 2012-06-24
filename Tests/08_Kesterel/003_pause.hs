-- Test 'pauseE' in combination with nothingE and >>>.
module T where

import Tests.KesterelBasis

correct c = property (\xs -> simulate c xs == zip terminated xs)
  where terminated = false : true : repeat false

constructive c = isJust (isConstructive c)

e0 = unitA >>> pauseE
c0 = runE e0

prop_c0 = correct c0
test_c0 = constructive c0

e1 = pauseE >>> nothingE
c1 = arr (\() -> ()) >>> runE e1

prop_c1 = correct c1
test_c1 = constructive c1

e2 = unitA >>> nothingE >>> pauseE >>> nothingE
c2 = runE e2

prop_c2 = correct c2
test_c2 = constructive c2

--------------------

e3 = unitA >>> nothingE >>> pauseE >>> nothingE >>> pauseE
c3 = runE e3

prop_c3 = property (\xs -> simulate c3 xs == zip terminated xs)
  where terminated = false : false : true : repeat false
test_c3 = constructive c3

e4 = unitA >>> nothingE >>> arr (\() -> ((), ())) >>> pauseE *** (pauseE >>> nothingE)
c4 = runE e4

prop_c4 = property (\xs -> simulate c3 xs == zip terminated xs)
  where terminated = false : false : true : repeat false

test_c4 = isJust (isConstructive c4)
