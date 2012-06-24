-- delay and combLoop interact appropriately.

module T where

import Prelude hiding ( id )
import Tests.Basis

-- screwed: initialisation is a combinational cycle.
c0 = proc () ->
  (| combLoop (\x ->
       do x' <- (| delayAC (returnA -< x) (trueA -< ()) |)
          dupA -< x' ) |)

prop_correct_c0 = property (\xs -> simulate c0 xs == take (length xs) (bottom : repeat true))
test_constructive_c0 = isNothing (isConstructive c0)
ok_netlist_c0 = runNL c0

-- screwed
c1 = proc () ->
      (| combLoop (\x ->
           do x' <- (| delayAC (returnA -< x) (trueA -< ()) |)
              y' <- (| delayAC (returnA -< x') (trueA -< ()) |)
              returnA -< (x', y') ) |)

prop_correct_c1 = property (\xs -> simulate c1 xs == take (length xs) (bottom : repeat true))
test_constructive_c1 = isNothing (isConstructive c1)
ok_netlist_c1 = runNL c1

-- OK
c2 = proc () ->
      (| combLoop (\y ->
           do x' <- (| delayAC (returnA -< y) (trueA -< ()) |)
              y' <- (| delayAC (falseA -< ()) (trueA -< ()) |)
              returnA -< (x', y') ) |)

prop_correct_c2 = property (\xs -> simulate c2 xs == take (length xs) (false : repeat true))
test_constructive_c2 = isJust (isConstructive c2)
ok_netlist_c2 = runNL c2

-- OK
c3 = proc () ->
      (| combLoop (\x ->
           do x' <- (| delayAC (orA <<< id *** trueA -< (x, ())) (trueA -< ()) |)
              returnA -< (x', x') ) |)

prop_correct_c3 = property (\xs -> simulate c3 xs == take (length xs) (repeat true))
test_constructive_c3 = isJust (isConstructive c3)
ok_netlist_c3 = runNL c3

-- OK
c4 = proc () ->
      do rec x <- (| delayAC (returnA -< y) (trueA -< ()) |)
             y <- (| delayAC (falseA -< ()) (trueA -< ()) |)
         returnA -< x

prop_correct_c4 = property (\xs -> simulate c4 xs == take (length xs) (false : repeat true))
test_constructive_c4 = isJust (isConstructive c4)
ok_netlist_c4 = runNL c4

-- screwed
c5 = proc () ->
      (| combLoop (\x ->
           do x' <- (| delayAC (falseA -< ()) (trueA -< ()) |)
              y' <- (| delayAC (orA -< (x, x')) (trueA -< ()) |)
              returnA -< (x', y') ) |)

prop_correct_c5 = property (\xs -> simulate c5 xs == take (length xs) (false : repeat true))
test_constructive_c5 = isNothing (isConstructive c5)
ok_netlist_c5 = runNL c5

-- screwed: the initialiser blows up.
c6 = proc () ->
       (| delayAC (| combLoop (\x -> dupA -< x) |) (trueA -< ()) |)

prop_correct_c6 = property (\xs -> simulate c6 xs == take (length xs) (bottom : repeat true))
test_constructive_c6 = isNothing (isConstructive c6)
ok_netlist_c6 = runNL c6

-- OK: c4 with x initially not y.
c7 = proc () ->
      do rec x <- (| delayAC (notA -< y) (trueA -< ()) |)
             y <- (| delayAC (falseA -< ()) (trueA -< ()) |)
         returnA -< x

prop_correct_c7 = property (\xs -> simulate c7 xs == take (length xs) (repeat true))
test_constructive_c7 = isJust (isConstructive c7)
ok_netlist_c7 = runNL c7
