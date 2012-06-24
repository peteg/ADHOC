-- Cyclic nand embedded in a non-constructive context.

module T where

import Tests.Basis

c = arr (\() -> ()) >>> trueA >>> combLoop (andA >>> notA >>> arr dupA)

prop_correct = property (\xs -> simulate c xs == take (length xs) (repeat bottom))

test_constructive = isNothing (isConstructive c)
