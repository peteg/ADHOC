-- The delayed true circuit works.

module T where

import Tests.Basis

nand_cycle = combLoop (andA >>> notA >>> arr (\a -> (a, a)))

c = arr (\() -> ()) >>> delayAC falseA trueA >>> nand_cycle

prop_correct = property (\xs -> simulate c xs == take (length xs) (true : repeat bottom))
test_constructive = isNothing (isConstructive c)
ok_netlist = runNL c
