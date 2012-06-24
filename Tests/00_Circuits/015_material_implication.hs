-- Material implication (x implies y).

module T where

import Tests.Basis

c = proc (x, y) ->
       do z <- orA <<< first notA -< (x, y)
	  returnA -< z

prop_correct = property (\(x, y) -> simulate c [(x, y)] == [x --> y])
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
