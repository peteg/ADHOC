module T where

import Tests.Basis

-- Constructivity is OK on this one.
c = proc a ->
  do rec x <- (| delayAC (falseA -< ()) (returnA -< y) |)
         y <- orA -< (a, x)
     returnA -< x

-- Constructivity loops on this one.
c' = proc a ->
   do rec x <- (| delayAC (falseA -< ()) (orA -< (a, x)) |)
      returnA -< x
-- Solution: make \/ lazy in its second argument in HBDD.

-- Constructivity still loops on this one.
c'' = proc a ->
   do rec x <- (| delayAC (falseA -< ()) (orA -< (x, a)) |)
      returnA -< x
-- Solution: use bOR and not \/.

-- Constructivity is OK on this one.
c''' = proc () ->
   do rec x <- (| delayAC (falseA -< ()) (notA -< x) |)
      returnA -< x

prop_correct = property $ \xs -> simulate c xs == simulate c' xs
prop_correct' = property $ \xs -> simulate c xs == simulate c'' xs

test_constructive = isJust (isConstructive c)
test_constructive' = isJust (isConstructive c')
test_constructive'' = isJust (isConstructive c'')
test_constructive''' = isJust (isConstructive c''')
