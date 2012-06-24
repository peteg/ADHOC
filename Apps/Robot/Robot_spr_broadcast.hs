{-# LANGUAGE Arrows, NoMonomorphismRestriction, TypeOperators #-}
{- The Robot example in circuits.
 - Copyright   :  (C)opyright 2006, 2009-2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -
 - ghc -O -main-is Robot_spr_broadcast.main -rtsopts -prof -package ADHOC Robot_spr_broadcast.hs
 - ghci -package ADHOC Robot_spr_broadcast.hs
 - mapM minimize kautos >>= dot
-}
module Robot_spr_broadcast where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude hiding ( id )

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

environment = proc halt ->
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
-- KBP.
-------------------------------------------------------------------

-- | The @Robot@ agent running a KBP.
robot = broadcast
          (mkSizedListSingletonA ("Robot", id, kTest ("Robot" `knows` probe "inGoal")))
          id
          id

-------------------------------------------------------------------
-- Robot top-level.
-------------------------------------------------------------------

robotTop = proc () ->
    do rec [halted] <- unSizedListA <<< robot -< sensor
           (pos, sensor) <- environment -< halted
       natA (undefined :: Three) -< pos
       returnA -< (halted, pos, sensor)

-------------------------------------------------------------------
-- Propositions.
-------------------------------------------------------------------

haltedp = arr (\(halted, _pos, _sensor) -> halted)

initiallySanep = proc (halted, pos, sensor) ->
    do a <- eqA <<< second (fromIntegerA 0) -< (pos, ())
       b <- orA <<< (eqA <<< second (fromIntegerA 0))
                &&& (eqA <<< second (fromIntegerA 1)) -< (sensor, ())
       c <- notA -< halted
       conjoinA 3 -< [a, b, c]

inGoalp = proc (_halted, pos, _sensor) ->
    do grcv <- goalRegionCentre -< ()
       (grlv, grrv) <- decA &&& incA -< grcv
       disjoinA 3 <<< mapA 3 eqA -< zip (repeat pos) [grlv, grcv, grrv]

pastGoalp = proc (_halted, pos, _sensor) ->
    do grrv <- incA <<< goalRegionCentre -< ()
       gtA -< (pos, grrv)

props = proc x ->
    do initiallySanev <- initiallySanep -< x
       haltedv <- haltedp -< x
       inGoalv <- probeA "inGoal" <<< inGoalp -< x
       pastGoalv <- pastGoalp -< x
       returnA -< (initiallySanev, haltedv, inGoalv, pastGoalv)

cprops = robotTop >>> props

-------------------------------------------------------------------
-- Model checking.
-------------------------------------------------------------------

Just (kautos, m, (initiallySane, halted, inGoal, pastGoal)) = broadcastSprSynth MinSTAMINA cprops
ctlM = mkCTLModel m

-- Sanity check the initial state.
test_initially_sane = isOK (mc ctlM (prop initiallySane))

-- Due to fairness we halt on all runs.
test_af_halt = isOK (mc ctlM (af (prop halted)))

-- At every instant it is still possible we might halt.
test_ag_ef_halt = isOK (mc ctlM (ag (ef (prop halted))))
test_neg_ag_ef_halt = not (isOK (mc ctlM (neg (ag (ef (prop halted))))))

-- We never make it past the goal region.
test_ag_neg_pastGoal = isOK (mc ctlM (ag (neg (prop pastGoal))))

-- If the robot halts, then it is in the goal region.
test_if_halts_in_goal = isOK (mc ctlM (ag (prop halted --> prop inGoal)))
test_not_if_in_goal_halted = not (isOK (mc ctlM (ag (prop halted <-- prop inGoal))))

-- 'halt' cannot stutter.
test_halt_stutter = not (isOK (mc ctlM (ef (prop halted /\ ef (neg (prop halted))))))

-- The robot does nothing until it halts for all time. The eventuality
-- holds due to fairness.
test_halt_permanent = isOK (mc ctlM ( (neg (prop halted) `au` ag (prop halted)) ))

-- ok_netlist = runNL cprops

-------------------------------------------------------------------
-- Profiling top-level.
-------------------------------------------------------------------

-- main = let ([bm], m') = broadcastSprSynth m in minimize bm >>= dot m
