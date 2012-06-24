module T where

import Tests.Basis

c =
    proc () ->
        do rec x <- notA <<< delayAC falseA returnA -< x
           returnA -< x

-- Check a relatively small number of sequence lengths.
test_correct =
  let prop n =
        let lhs = repeat ()
            rhs = cycle [true, false]
          in take n (simulate c lhs) == take n rhs
   in and (map prop [0..100])

test_constructive = isJust (isConstructive c)
