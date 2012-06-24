{-# LANGUAGE Arrows, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, NoMonomorphismRestriction, RankNTypes, TypeOperators, UndecidableInstances #-}
{- A puzzle from Raymond Smullyan's "The Lady or the Tiger?", OUP, 1982.
 - Copyright   :  (C)opyright 2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -
 - ghc -Wall -O -main-is MetaPuzzle3.main -rtsopts -prof -package ADHOC MetaPuzzle3.hs
 - ghci -package ADHOC MetaPuzzle3.hs
 -
 -}
module MetaPuzzle3 where

-------------------------------------------------------------------
-- Dependencies
-------------------------------------------------------------------

import Prelude hiding ( id, (.) )

import ADHOC
import ADHOC.NonDet

import ADHOC.ModelChecker.CTL as CTL
import ADHOC.ModelChecker.CounterExamples

import ADHOC.Knowledge

-------------------------------------------------------------------
-- The puzzle.
-------------------------------------------------------------------

{-

p93:

3. A Knight-Knave Metapuzzle.

My book /What is the name of this book?/ contains a host of puzzles
about an island on which every inhabitant is either a knight or a
knave; knights always tell the truth and knaves always lie. Here is a
knight-knave metapuzzle.

A logician once visited this island and came across two inhabitants, A
and B. He asked A, "Are both of you knights?" A answered either yes or
no. The logician thought for a while but did not yet have enough
information to determine what they were. The logician then asked A,
"Are you two of the same type?" (Same type means both knights or both
knaves.) A answered either yes or no, and the logician then knew what
type each was.

What type is each?

-}

-- | An inhabitant is either a knight or a knave.
type Inhabitant b = b

is_a_knightA, is_a_knaveA :: ArrowComb (~>) => B (~>) ~> B (~>)
is_a_knightA = id
is_a_knaveA = notA

-- | The system state: the type of the two inhabitants.
type State b = (Inhabitant b, Inhabitant b)

inhabitant_a, inhabitant_b :: State b -> Inhabitant b
inhabitant_a = fst
inhabitant_b = snd

logician :: AgentID
logician = "logician"

a_is_a_knight, b_is_a_knight :: ProbeID
a_is_a_knight = "A is a knight"
b_is_a_knight = "B is a knight"

{-

We need to model the temporal dimension here.

As we don't care about the epistemic states of inhabitants A and B, we
model only the logician as an agent.

-}

-- | The questions are answered in succeeding instants.
answersA = proc s ->
  do -- A tells the truth iff he is a knight.
     a_tells_the_truth <- is_a_knightA -< inhabitant_a s

     -- FIXME cheesy: we should probably have 3 states, not just 2: a1, a2, finished.
     (| muxAC (isInitialState -< ())
          ( -- 1 (to A): Are both of you knights?
           (returnA -< a_tells_the_truth)
             `iffAC` ((is_a_knightA -< inhabitant_a s) `andAC` (is_a_knightA -< inhabitant_b s)))
          ( -- 2 (to A): Are you two of the same type?
           (returnA -< a_tells_the_truth)
             `iffAC` ((is_a_knightA -< inhabitant_a s) `iffAC` (is_a_knightA -< inhabitant_b s))) |)

-- | At each instant the logician decides whether he knows the types
-- of A and B.
logicianA = agent logician $ kTest $
     (logician `knows_hat` a_is_a_knight)
  /\ (logician `knows_hat` b_is_a_knight)

top = proc () ->
  do -- All states are initially plausible.
     s <- nondetLatchAC trueA -< ()

     probeA a_is_a_knight <<< is_a_knightA -< inhabitant_a s
     probeA b_is_a_knight <<< is_a_knightA -< inhabitant_b s

     -- Pipe the answers to the logician.
     logicianA <<< answersA -< s

-------------------------------------------------------------------
-- Synthesis and model checking.
-------------------------------------------------------------------

-- Clock won't work here, we need to remember what was said.
Just (kautos, m, lout) = singleSPRSynth MinNone top
ctlM = mkCTLModel m

-- We want the initial state(s) where the dialogue went to plan.
--
-- The logician initially doesn't know, then does.
dialogue_result = showWitness ctlM (neg (prop lout) /\ ex (prop lout))
test_mc = isOK (CTL.mc ctlM ((neg (prop lout) /\ ex (prop lout))
                          --> (neg (probe a_is_a_knight) /\ neg (probe b_is_a_knight))))
test_mc_non_trivial = not (isOK (CTL.mc ctlM (neg (neg (prop lout) /\ ex (prop lout)))))

-- Answer: A and B are both knaves.

-- The answer is not canonical in this straightforward way:.
test_mc_canonical_naive = not (isOK (CTL.mc ctlM (ag (prop lout --> (neg (probe a_is_a_knight) /\ neg (probe b_is_a_knight))))))
canonical_naive_counterexample = showCounterExample ctlM (ag (prop lout --> (neg (probe a_is_a_knight) /\ neg (probe b_is_a_knight))))

-- ... because the logician would know A is a knight and B is a knave
-- in the initial state if he gets the answer "no".
