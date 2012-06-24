-- Example from Shiple/Berry/Touati "Constructive Analysis of Cyclic Circuits".
-- The recursion is a bit clunky but adequate for Esterel ??

module T where

import Tests.Basis

c = proc (x, y, z) ->
      (| combLoop (\d ->
        (| combLoop (\e ->
          do r <- andA -< (x, d)
             a <- andA <<< first andA -< ((y, r), e)
             d' <- orA -< (z, a)
             e' <- andA -< (r, d)
             returnA -< (((a, e), d'), e') ) |) ) |)

prop_correct =
    property (\(x, y, z) -> all (/= bottom) [x, y, z]
                              ==> simulate c [(x, y, z)] == [res x y z])
  where res x y z
            | x /\ y /\ neg z == true = (bottom, bottom)
            | x /\ neg y /\ z == true = (false, true)
            | x /\ y /\ z == true = (true, true)
            | otherwise = (false, false)

-- Actually constructive except for input (1,1,0)
test_constructive = isNothing (isConstructive c)
