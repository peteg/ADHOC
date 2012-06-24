-- Looped XOR, using combLoop rather than loop.

module T where

import Tests.Basis

c =
    let
      arrow =
        proc ((x, y), z1) ->
	  do z0  <- orA  -< (x, y)
	     z2  <- andA <<< second notA -< (z0, z1)
	     z1' <- andA -< (x, y)
	     returnA -< (z2, z1')
    in combLoop arrow

prop_correct = property (\(x, y) -> simulate c [(x, y)] == [x `xor` y])

test_constructive = isJust (isConstructive c)
