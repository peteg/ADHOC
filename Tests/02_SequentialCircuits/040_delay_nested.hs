{-# LANGUAGE Arrows, FlexibleContexts, NoMonomorphismRestriction, RankNTypes, TypeOperators #-}
-- nested delays, ensure things get initialised and propagated appropriately.

module T where

-- We're checking the Constructivity interpretation, so we need the model checker...
import Tests.ModelCheckerBasis

inner = "inner"
outer = "outer"

c = unitA >>> delayAC falseA (delayAC trueA falseA >>> probeA inner) >>> probeA outer

prop_correct = property (\xs -> simulate c xs == take (length xs) (false : true : repeat false))
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c

Just (m, out) = isConstructive c
ctlM = mkCTLModel m

-- Same property as prop_correct.
test_outer = isOK (mc ctlM (neg (probe outer) /\ ax (probe outer /\ ax (ag (neg (probe outer))))))
test_inner = isOK (mc ctlM ((probe inner) /\ ax (ag (neg (probe inner)))))
