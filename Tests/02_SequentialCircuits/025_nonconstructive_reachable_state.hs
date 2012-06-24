-- A circuit that is constructive in the initial state but not in the second.

module T where

import Tests.Basis

c = proc () ->
      do boot <- delayAC falseA trueA -< ()
         combLoop (dupA <<< notA <<< andA) -< boot

-- Check a relatively small number of sequence lengths.
test_correct =
  let prop n =
        let lhs = repeat ()
            rhs = true : repeat bottom
          in take n (simulate c lhs) == take n rhs
   in and (map prop [0..100])

test_constructive = isNothing (isConstructive c)
ok_netlist = runNL c
