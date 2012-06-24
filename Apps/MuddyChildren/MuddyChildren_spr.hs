{-# LANGUAGE Arrows, FlexibleContexts, NoMonomorphismRestriction, RankNTypes, TypeOperators #-}
{- The Muddy Children puzzle in circuits.
 - Copyright   :  (C)opyright 2009-2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -
 - ghci -package ADHOC MuddyChildren_spr.hs
 - dot kautos
 -
 - ghc -O -main-is Main.main -rtsopts -prof -auto-all -caf-all -package ADHOC MuddyChildren_spr.hs
 -
 -}
module MuddyChildren_spr where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude hiding ( id, (.), mapM )

import Data.List ( genericReplicate )

import ADHOC
import ADHOC.Knowledge
import ADHOC.ModelChecker.CTL
import ADHOC.ModelChecker.CounterExamples
import ADHOC.Patterns
import ADHOC.NonDet

-------------------------------------------------------------------
-- Parameters.
-------------------------------------------------------------------

type NumChildren = Three

num_children :: Integer
num_children = c2num (undefined :: NumChildren)

childName :: Integer -> AgentID
childName i = "child_" ++ show i

all_children_say_yesP :: ProbeID
all_children_say_yesP = "all children say yes"

dirtyP :: Integer -> ProbeID
dirtyP i = "child_" ++ show i ++ "_is_dirty"

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
     mapSLn (probeA . dirtyP) -< d
     anyDirty <- disjoinSL -< d
     -- Initially the children say they do not know whether they are
     -- muddy (they have not been asked).
     rec acts <- (| delayAC (replicateSL <<< falseA -< ())
                             (| (broadcast childAs)
                                  (returnA -< (anyDirty, d `asLengthOf` acts))
                                  (returnA -< acts) |) |)
     idSL (undefined :: NumChildren) -< d
     probeA all_children_say_yesP <<< conjoinSL -< acts

-------------------------------------------------------------------
-- Synthesis and model checking.
-------------------------------------------------------------------

-- Synthesis using the SPR semantics
-- Just (kautos, m, _) = broadcastSprSynth MinNone environment
Just (kautos, m, _) = broadcastSprSynth MinBisim environment
-- Just (kautos, m, _) = broadcastSprSynth MinSTAMINA environment
ctlM = mkCTLModel m

-- The muddiness of the children is constant.
test_muddiness_constant =
    isOK (mc ctlM (conjoin [ ag (p <-> ax p)
                           | i <- [1 .. num_children]
                           , let p = probe (dirtyP i) ]))

-- | All children eventually say 'yes'.
-- FIXME verify: this only works for 3 children.
test_children_eventually_say_yes =
    isOK (mc ctlM (af (probe all_children_say_yesP)))

-- | Clock semantics (not spr): once the children say 'yes', they immediately
-- forget they knew their muddiness.
test_children_forget =
    isFailure (mc ctlM (ag (probe all_children_say_yesP --> ax (neg (probe all_children_say_yesP)))))

specs = [ sOK "eventually say yes" $ af (probe all_children_say_yesP) ]

main =
  do m `seq` putStrLn "System is constructive!"
     mcce ctlM specs
