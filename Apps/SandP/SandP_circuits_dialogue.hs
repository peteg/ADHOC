{-# LANGUAGE Arrows, FlexibleContexts, NoMonomorphismRestriction, RankNTypes, ScopedTypeVariables, TypeOperators #-}
{-   The Mr S(um) and Mr P(roduct) puzzle analysed by McCarthy, and van
 -   Ditmarsch, Ruan, Verbrugge.
 - Copyright   :  (C)opyright 2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -
 - ghc -O -main-is Main.main -rtsopts -prof -auto-all -caf-all -package ADHOC SandP_circuits_dialogue.hs
 -
 - For some reason ghc 7.0.3 does a terrible job *without* profiling.
 - ghc -O -main-is Main.main -rtsopts -package ADHOC SandP_circuits_dialogue.hs
 - ghci -package ADHOC SandP_circuits_dialogue.hs
 -

BDDs blow up on multipliers, and more specifically, when we try to
quotient the initial states under multiplication. This version adds
the multiplication to the states so that Mr. P's observation is simply
equality.

The game is to define a dialogue combinator that supports an abstract
description.

The puzzle according to McCarthy:

Two numbers m and n are chosen such that 2 ≤ m ≤ n ≤ 99. Mr. S is told
their sum and Mr. P is told their product. The following dialogue
ensues:

Mr. P: I don’t know the numbers.
Mr. S: I knew you didn’t know. I don’t know either.
Mr. P: Now I know the numbers.
Mr. S: Now I know them too.

In view of the above dialogue, what are the numbers?

http://www-formal.stanford.edu/jmc/puzzles/puzzles.html

-}

module Main ( main ) where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude hiding ( (.), id )

import ADHOC
import ADHOC.Data.Arithmetic
import ADHOC.NonDet

import ADHOC.Knowledge

import ADHOC.ModelChecker.CTL as CTL
import ADHOC.ModelChecker.CounterExamples

import Dialogue

-------------------------------------------------------------------

disjoinAC :: ArrowComb (~>) => ([env ~> B (~>)]) -> (env ~> B (~>))
disjoinAC = foldr (\f fs -> proc env -> ((f -< env) `orAC` (fs -< env))) falseA

natAW = natA (undefined :: Seven)
natAWM = natA (undefined :: Fourteen)

-------------------------------------------------------------------
-- The scenario.
-------------------------------------------------------------------

mrS :: AgentID
mrS = "Mr. S."

mrP :: AgentID
mrP = "Mr. P."

mP, nP, mrSactP, mrPactP :: ProbeID
mP = "m"
nP = "n"
mrSactP = "mrS says"
mrPactP = "mrP says"

-- | An agent knows the two values.
knows_mn :: AgentID -> KF
knows_mn aid = aid `knows_hat` mP /\ aid `knows_hat` nP

-- | Initially Mr. S is told their sum and Mr. P is told their product.
agent_init_arrs = mkSizedListA
  [ (mrS, numCastA <<< addA <<< arr fst)
  , (mrP, arr snd) ]
      `withLength` (undefined :: Two)

dialogue :: Dialogue Four
dialogue = mkSizedListA
  [
    -- Mr. P: I don’t know the numbers.
    mrP :> now (neg (knows_mn mrP))
    -- Mr. S: I knew you didn’t know. I don’t know either.
  , mrS :> pre (mrS `knows` neg (knows_mn mrP))
        /\ now (neg (knows_mn mrS))
    -- Mr. P: Now I know the numbers.
  , mrP :> now (knows_mn mrP)
    -- Mr. S: Now I know them too.
  , mrS :> now (knows_mn mrS)
  ]

top = proc () ->
  do (mn, p) <- (| nondetLatchAC (\s0 -> disjoinAC initAs -< s0) |)
     acts <- runDialogue agent_init_arrs dialogue -< (mn, p)
     let [mrSact, mrPact] = unSizedListA acts
     probeA mP *** probeA nP -< mn
     probeA mrSactP *** probeA mrPactP -< (mrSact, mrPact)
  where
    initAs = [ proc ((m, n), p) ->
                         ( ((natAW -< m) `eqAC` (fromIntegerA vm -< ()))
                   `andAC` ((natAW -< n) `eqAC` (fromIntegerA vn -< ()))
                   `andAC` ((natAWM -< p) `eqAC` (fromIntegerA (vm * vn) -< ())) )
             | vm <- [ 2 .. 99 ], vn <- [ vm .. 99 ] ]

-------------------------------------------------------------------
-- Synthesis and model checking.
-------------------------------------------------------------------

-- Synthesis using the SPR semantics
-- Don't run stamina, we don't have all day.
Just (kautos, m, _) = broadcastSprSynth MinBisim top
-- Just (kautos, m, _) = broadcastSprSynth MinNone top
ctlM = mkCTLModel m

-- We want the initial state(s) where the dialogue went to plan.
-- This is where all (four of) the announcements came out true.
--dialogue_result = showWitness ctlM (ex (ex (p /\ ex (p /\ ex (p /\ ex p)))))
dialogue_result = showCounterExample ctlM (af (neg p))
  where p = probe mrSactP /\ probe mrPactP

-- | This example is big enough that we need to compile it...  It
-- seems that ReorderStableWindow3 is faster than ReorderSift.
main :: IO ()
main =
  do dynamicReordering ReorderStableWindow3 -- ReorderSift -- ReorderStableWindow3
     -- print m
     -- print test_dialogue
--     dot kautos
     dialogue_result
