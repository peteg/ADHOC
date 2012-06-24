-- A circuit that is constructive in all states.

module T where

import Tests.Basis

c = proc () ->
      do boot <- delayAC falseA falseA -< ()
         combLoop (dupA <<< notA <<< andA) -< boot

test_correct = take n (simulate c lhs) == take n rhs
    where
      n = 50
      lhs = repeat ()
      rhs = repeat true

test_constructive = isJust (isConstructive c)

ok_netlist = runNL c
