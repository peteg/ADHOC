{-# LANGUAGE Arrows, FlexibleContexts, NoMonomorphismRestriction, RankNTypes, TypeOperators #-}
{- The Muddy Children puzzle in circuits.
 - Copyright   :  (C)opyright 2009-2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -
 - ghci -package ADHOC MuddyChildren_clock.hs
 -
 - dot kautos
 - test_children_forget
 -
 -}
module MuddyChildren_clock where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude hiding ( id, (.) )

import ADHOC
import ADHOC.NonDet
import ADHOC.ModelChecker.CTL

import ADHOC.Knowledge

-------------------------------------------------------------------
-- Parameters.
-------------------------------------------------------------------

type NumChildren = Three

num_children :: Integer
num_children = c2num (undefined :: NumChildren)

childName :: Integer -> String
childName i = "child_" ++ show i

dirtyP :: Integer -> String
dirtyP i = "child_" ++ show i ++ "_is_dirty"

dirtyProbe :: ArrowProbe (~>) (B (~>)) => Integer -> B (~>) ~> B (~>)
dirtyProbe i = probeA (dirtyP i)

-------------------------------------------------------------------
-- The children.
-------------------------------------------------------------------

-- | Child /i/ can observe the dirtiness of all the other children,
-- but not herself.
--
-- Each child simply runs a KBP.
childAs = mkSizedListf (\i -> (childName i, childInitObs i, childA i))
  where
    childA i = kTest (childName i `knows_hat` dirtyP i)
    childInitObs i = second (mapSLn (\j -> if i == j then zeroA else id))

-------------------------------------------------------------------
-- Muddy children top-level: environment/father.
-------------------------------------------------------------------

environment = proc () ->
  do -- Initially: non-deterministically choose some children to be
     -- dirty and fix these for all time.
     d <- nondetLatchAC trueA -< ()
     mapSLn dirtyProbe -< d
     anyDirty <- disjoinSL -< d
     -- Initially the children say they do not know whether they are
     -- muddy (they have not been asked).
     rec acts <- (| delayAC (replicateSL <<< falseA -< ())
                             (| (broadcast childAs)
                                  (returnA -< (anyDirty, d `asLengthOf` acts))
                                  (returnA -< acts) |) |)
     idSL (undefined :: NumChildren) -< d
     returnA -< (anyDirty, d, acts)

-------------------------------------------------------------------
-- Propositions.
-------------------------------------------------------------------

all_children_say_yesp = proc (anyDirty, d, acts) ->
  conjoinSL -< acts

props = proc x ->
  do all_children_say_yesv <- all_children_say_yesp -< x
     returnA -< (all_children_say_yesv)

cprops = environment >>> props

-------------------------------------------------------------------
-- Synthesis and model checking.
-------------------------------------------------------------------

-- Synthesis using the clock semantics
-- Just (kautos, m, all_children_say_yes) = clockSynth MinNone cprops
-- Just (kautos, m, all_children_say_yes) = clockSynth MinBisim cprops
Just (kautos, m, all_children_say_yes) = clockSynth MinSTAMINA cprops
ctlM = mkCTLModel m

-- | The muddiness of the children is constant.
test_muddiness_constant =
    isOK (mc ctlM (conjoin [ ag (p <-> ax p)
                           | i <- [1 .. num_children]
                           , let p = probe (dirtyP i) ]))

-- | All children eventually say 'yes'. Not true for the clock semantics.
test_children_eventually_say_yes =
    isFailure (mc ctlM (af (prop all_children_say_yes)))

-- | Clock semantics: once the children say 'yes', they immediately
-- forget they knew their muddiness.
test_children_forget =
    isOK (mc ctlM (ag (prop all_children_say_yes --> ax (ax (neg (prop all_children_say_yes))))))
