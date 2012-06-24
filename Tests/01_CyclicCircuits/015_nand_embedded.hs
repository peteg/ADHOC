-- Cyclic nand embedded in a constructive context.

module T where

import Tests.Basis

c = unitA >>> falseA >>> combLoop (andA >>> notA >>> arr dupA)

prop_correct = property (\xs -> simulate c xs == take (length xs) (repeat true))

test_constructive = isJust (isConstructive c)
