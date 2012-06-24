module T where

import Tests.Basis

c = proc () ->
        (| combLoop (\x ->
             do x' <- (| delayAC (falseA -< ()) (returnA -< x) |)
                dupA <<< notA -< x'
          ) |)

prop_correct = take n (simulate c lhs) == take n rhs
    where
      n = 100
      lhs = repeat ()
      rhs = cycle [true, false]

test_constructive = isJust (isConstructive c)
