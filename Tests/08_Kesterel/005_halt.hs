module T where

import Tests.KesterelBasis

e = haltE
c = unitA >>> runE e

prop_correct = property (\xs -> simulate c xs == zip (repeat false) xs)
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c

-- Equivalent (but fatter) circuit

e' = unitA >>> loopE (pauseE >>> pauseE)
c' = runE e'

ok_netlist' = runNL c'
prop_correct' = property (\xs -> simulate c xs == simulate c' xs)
ok_constructive' = isJust (isConstructive c)
