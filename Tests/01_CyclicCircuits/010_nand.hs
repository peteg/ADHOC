-- Cyclic nand, constructive with input 'false'.

module T where

import Tests.Basis

c = combLoop (andA >>> notA >>> arr dupA)

prop_correct = property (\xs -> simulate c xs == map res xs)
    where res x = if x == false then true else bottom

test_constructive = isNothing (isConstructive c)
