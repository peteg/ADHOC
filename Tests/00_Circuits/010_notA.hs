-- The negation circuit works. Fewer types this time.

module T where

import Tests.Basis

c = notA

prop_correct = property (\xs -> simulate c xs == map neg xs)
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
