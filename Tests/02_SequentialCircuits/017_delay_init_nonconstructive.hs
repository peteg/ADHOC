-- Initialise a delay with a non-constructive circuit.

module T where

import Tests.Basis

c = unitA >>> delayAC (combLoop (dupA <<< notA <<< andA) <<< trueA) falseA

test_correct =
  let prop n =
        let lhs = repeat ()
            rhs = bottom : repeat false
          in take n (simulate c lhs) == take n rhs
   in and (map prop [0..100])

test_constructive = isNothing (isConstructive c)
ok_netlist = runNL c
