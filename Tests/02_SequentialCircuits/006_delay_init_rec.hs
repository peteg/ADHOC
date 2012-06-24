-- delay and loop interact appropriately.

module T where

import Prelude hiding ( id )
import Tests.Basis

-- screwed: initialisation via loop.
-- fortunately for us, Constructivity terminates.
-- unfortunately Simulate doesn't.
c0 = proc () ->
  do rec x <- (| delayAC (returnA -< x) (trueA -< ()) |)
     returnA -< x

-- prop_correct_c0 = property (\xs -> simulate c0 xs == take (length xs) (bottom : repeat true))
test_constructive_c0 = isNothing (isConstructive c0)

-- screwed
c1 = proc () ->
  do rec x <- (| delayAC (returnA -< y) (trueA -< ()) |)
         y <- (| delayAC (returnA -< x) (trueA -< ()) |)
     returnA -< x

-- prop_correct_c1 = property (\xs -> simulate c1 xs == take (length xs) (bottom : repeat true))
test_constructive_c1 = isNothing (isConstructive c1)
