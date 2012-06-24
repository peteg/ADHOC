module T where

import Tests.KesterelBasis

-- Exception is thrown, so we terminate in the first instant.
e = catchE $ \e -> throwE e >>> pauseE
c = idB >>> runE e

prop_correct = property (\xs -> simulate c xs == take (length xs) (zip (true : repeat false) (repeat ())))
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c

-- If not thrown, we terminate in the second instant.
e1 = catchE $ \e -> pauseE
c1 = idB >>> runE e1

prop_correct1 = property (\xs -> simulate c1 xs == take (length xs) (zip (false : true : repeat false) (repeat ())))
test_constructive1 = isJust (isConstructive c1)
ok_netlist1 = runNL c1
