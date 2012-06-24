-- Example from Shiple/Berry/Touati "Constructive Analysis of Cyclic Circuits".
-- Simplified slightly: reduce it to two inputs, eliminating the
-- 3-input AND gate.
-- The probes show that it takes 3 iterations to reach a fixpoint.
--   sim c [(true, true)]

module T where

import Tests.Basis

c = proc (x, z) ->
      (| combLoop (\d ->
        (| combLoop (\e ->
          do probeA "d" -< d
             probeA "e" -< e
             r <- andA -< (x, d)
             a <- andA -< (r, e)
             d' <- orA -< (z, a)
             e' <- andA -< (r, d')
             returnA -< (((a, e), d'), e') ) |) ) |)

prop_correct =
    property (\(x, z) -> all (/= bottom) [x, z]
                            ==> simulate c [(x, z)] == [res x z])
  where res x z
            | x /\ neg z == true = (bottom, bottom)
            | x /\ z == true = (true, true)
            | otherwise = (false, false)

-- Actually constructive except for input (1,1,0)
test_constructive = isNothing (isConstructive c)
ok_netlist = runNL c
