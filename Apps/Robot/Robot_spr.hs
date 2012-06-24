{-# LANGUAGE Arrows, NoMonomorphismRestriction, TypeOperators #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{- The Robot example in circuits.
 - Copyright   :  (C)opyright 2006, 2009-2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -
 - ghci -package ADHOC Robot.hs
 - dot kautos
 -
 - FIXME variant: move back and forth, start in any position.
 - FIXME variant: start in either 0,1,2. ???
 - FIXME variant: goal of wdith 2.
 -}
module Robot_spr where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import ADHOC
import ADHOC.NonDet
import ADHOC.Data.Arithmetic
import ADHOC.Patterns
import ADHOC.ModelChecker.CTL

import ADHOC.Knowledge

-------------------------------------------------------------------
-- Parameters.
-------------------------------------------------------------------

goalRegionCentre :: ArrowNum (~>) n => () ~> n
goalRegionCentre = fromIntegerA 3

-------------------------------------------------------------------
-- An implementation of the environment.
--
-- Non-deterministically move right or stay still, unless the robot
-- has signalled it wishes to stop. Update the sensor with a reading
-- within 1 unit of the present position.
--
--   - Need to have the robot's halt instantaneously responded to.
-------------------------------------------------------------------

environment =
    proc halt ->
      do rec pos <- (| delayAC
                         (fromIntegerA 0 -< ())
                         (| muxAC (returnA -< halt)
                              (returnA -< pos)
                              (| nondetFairAC (returnA -< pos)
                                              (incA -< pos) |) |) |)
         (posP, posS) <- decA &&& incA -< pos
         sensor <- nondetListA 3 -< [posP, pos, posS]
         returnA -< (pos, sensor)

-------------------------------------------------------------------
-- An implementation of the robot's protocol.
-------------------------------------------------------------------

-- | IncAomplete test: if the sensor reads 'goalRegionCentre' then we
-- halt, otherwise not.
robotTestEq =
  proc sensor -> eqA <<< second goalRegionCentre -< (sensor, ())

-- | Complete test: if the sensor reads 'goalRegionCentre' or greater,
-- then we halt, otherwise not. This can stutter, i.e. inifinitely
-- alternate between halted and not-halted.
robotTestGEq =
  proc sensor -> geA <<< second goalRegionCentre -< (sensor, ())

-- | Synthesis.
robotTestKBP = kTest ("Robot" `knows` probe "inGoal")

-- | The @Robot@ agent.
robot test = agent "Robot" test

-------------------------------------------------------------------
-- Robot top-level.
-------------------------------------------------------------------

robotTop =
  proc () ->
--     do rec halted <- robot robotTestGEq -< sensor
    do rec halted <- robot robotTestKBP -< sensor
           (pos, sensor) <- environment -< halted
       natA (undefined :: Three) -< pos
       returnA -< (halted, pos, sensor)

-------------------------------------------------------------------
-- Propositions.
-------------------------------------------------------------------

haltedp = arr (\(halted, _pos, _sensor) -> halted)

initiallySanep =
  proc (halted, pos, sensor) ->
    do a <- eqA <<< second (fromIntegerA 0) -< (pos, ())
       b <- orA <<< (eqA <<< second (fromIntegerA 0))
                &&& (eqA <<< second (fromIntegerA 1)) -< (sensor, ())
       c <- notA -< halted
       conjoinA 3 -< [a, b, c]

inGoalp =
  proc (_halted, pos, _sensor) ->
    do grcv <- goalRegionCentre -< ()
       (grlv, grrv) <- decA &&& incA -< grcv
       disjoinA 3 <<< mapA 3 eqA -< zip (repeat pos) [grlv, grcv, grrv]

pastGoalp =
  proc (_halted, pos, _sensor) ->
    do grrv <- incA <<< goalRegionCentre -< ()
       gtA -< (pos, grrv)

props =
  proc x ->
    do initiallySanev <- initiallySanep -< x
       haltedv <- haltedp -< x
       inGoalv <- probeA "inGoal" <<< inGoalp -< x
       pastGoalv <- pastGoalp -< x
       returnA -< (initiallySanev, haltedv, inGoalv, pastGoalv)

cprops = robotTop >>> props

-------------------------------------------------------------------
-- Model checking.
-------------------------------------------------------------------

-- Just (kautos, m, (initiallySane, halted, inGoal, pastGoal)) = singleSPRSynth MinNone cprops
-- Just (kautos, m, (initiallySane, halted, inGoal, pastGoal)) = singleSPRSynth MinBisim cprops
Just (kautos, m, (initiallySane, halted, inGoal, pastGoal)) = singleSPRSynth MinSTAMINA cprops
ctlM = mkCTLModel m

-- Sanity check the initial state.
test_initially_sane = isOK (mc ctlM (prop initiallySane))

-- Fairness: we always halt.
test_neg_af_halt = isOK (mc ctlM (af (prop halted)))

-- At every instant it is still possible we might halt.
test_ag_ef_halt = isOK (mc ctlM (ag (ef (prop halted))))
test_neg_ag_ef_halt = not (isOK (mc ctlM (neg (ag (ef (prop halted))))))

-- We never make it past the goal region.
test_ag_neg_pastGoal = isOK (mc ctlM (ag (neg (prop pastGoal))))

-- If the robot halts, then it is in the goal region.
test_if_halts_in_goal = isOK (mc ctlM (ag (prop halted --> prop inGoal)))
test_not_if_in_goal_halted = not (isOK (mc ctlM (ag (prop halted <-- prop inGoal))))

-- 'halt' can stutter as it is not latched (the 'bicycle brake' halt model).
-- This is true for the stateless and clock implementations, false for SPR.
-- test_halt_stutter = isOK (mc ctlM (ef (prop halted /\ ef (neg (prop halted)))))
-- For SPR we halt for all time on every path.
test_halt_stutter = isOK (mc ctlM (af (ag (prop halted))))

-- The robot does nothing until it halts for all time.

-- FIXME This should be true for SPR, false for the stateless and
-- clock implementations, but requires a fairness constraint: it is
-- not true if e.g. the robot never moves from position 0.
test_halt_permanent = isOK (mc ctlM ( (neg (prop halted) `au` ag (prop halted)) ))

-- ok_netlist = runNL cprops

{-
     (
      "The robot halts if it knows its in the goal region.",
      ag ctlM (halt <== knowsObs ctlM "Robot" inGoalProbe),
      true
     ),
     (
      "The robot halts only if it knows its in the goal region.",
      ag ctlM (halt ==> knowsObs ctlM "Robot" inGoalProbe),
      true
     )

-}
