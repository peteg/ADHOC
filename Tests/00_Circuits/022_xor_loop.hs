-- XOR using a harmless loop.

module T where

import Tests.Basis

c = proc (x, y) ->
      do rec z2 <- andA <<< second notA -< (z0, z1)
	     z0 <- orA  -< (x, y)
	     z1 <- andA -< (x, y)
	 returnA -< z2

prop_correct = property (\(x, y) -> simulate c [(x, y)] == [x `xor` y])
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
