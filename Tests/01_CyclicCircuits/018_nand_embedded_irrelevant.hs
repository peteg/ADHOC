-- Cyclic nand embedded in a non-constructive and irrelevant context.
-- Demonstrates the difference between /strong/ and /weak/ constructivity.

module T where

import Tests.Basis

c = combLoop (andA >>> notA >>> arr dupA) >>> arr (const ()) >>> falseA

prop_correct = property (\xs -> simulate c xs == take (length xs) (repeat false))

test_constructive = isNothing (isConstructive c)
