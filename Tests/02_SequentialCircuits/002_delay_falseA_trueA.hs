{-# LANGUAGE Arrows, FlexibleContexts, NoMonomorphismRestriction, RankNTypes, TypeOperators #-}
-- false followed by true works.

module T where

import Tests.Basis

c = arr (\() -> ()) >>> delayAC falseA trueA

prop_correct = property (\xs -> simulate c xs == take (length xs) (false : repeat true))
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
