-- Same as 035_delay_rec, but using combLoop instead.
module T where

import Tests.Basis

c = proc a ->
      (| combLoop (\y ->
           do x <- (| delayAC (falseA -< ()) (returnA -< y) |)
              y <- orA -< (a, x)
              returnA -< (x, y)) |)

c' = proc a ->
       (| combLoop (\x ->
            do x' <- (| delayAC (falseA -< ()) (orA -< (a, x)) |)
               returnA -< (x', x')) |)

c'' = proc a ->
       (| combLoop (\x ->
            do x' <- (| delayAC (falseA -< ()) (orA -< (x, a)) |)
               returnA -< (x', x')) |)

-- Constructivity is OK on this one.
c''' = proc () ->
       (| combLoop (\x ->
            do x' <- (| delayAC (falseA -< ()) (notA -< x) |)
               returnA -< (x', x')) |)

test_constructive = isJust (isConstructive c)
test_constructive' = isJust (isConstructive c')
test_constructive'' = isJust (isConstructive c'')
test_constructive''' = isJust (isConstructive c''')
