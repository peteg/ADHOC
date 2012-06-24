{-# LANGUAGE Arrows, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, NoMonomorphismRestriction, RankNTypes, TypeOperators, UndecidableInstances #-}
{- A puzzle from Raymond Smullyan's "The Lady or the Tiger?", OUP, 1982.
 - Copyright   :  (C)opyright 2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -
 - ghc -Wall -O -main-is MetaPuzzle2.main -rtsopts -prof -package ADHOC MetaPuzzle2.hs
 - ghci -package ADHOC MetaPuzzle2.hs
 -
 -}
module MetaPuzzle2 where

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

p92:

2. A Transylvanian Metapuzzle

We learned from Chapter 4 that every Transylvanian is one of four
types: (1) a sane human; (2) an insane human; (3) a sane vampire; (4)
an insane vampire. Sane humans make only true statements (they are
both accurate and honest); insane humans make only false statements
(out of delusion, not intention); sane vampires make only false
statements (out of dishonesty, not delusion); and insane vampires make
only true statements (they believe the statement is false, but lie and
say the statement is true).

Three logicians were once discussing their separate trips to
Transylvania.

"When I was there," said the first logician, "I met a Transylvanian
named Igor. I asked him whether he was a sane human. Igor answered me
[yes or no], but I couldn't tell from his answer what he was."

"That's a surprising coincidence," said the second logician. "I met
that same Igor on /my/ visit. I asked him whether he was a sane
vampire and he answered me [yes or no], and I couldn't figure out what
he was."

"This is a double coincidence!" exclaimed the third logician. "I also
met Igor and asked him whether he was an insane vampire. He answered
me [yes or no], and I couldn't deduce what he was either."

Is Igor sane or insane? Is he a human or a vampire?

-}


-- | Igor is sane/insane, a person/vampire.
type Igor b = (b, b)

igor_is_saneA = arr fst
igor_is_insaneA = arr fst >>> notA
igor_is_humanA = arr snd
igor_is_vampiricA = arr snd >>> notA

logician1, logician2, logician3 :: AgentID
logician1 = "logician 1"
logician2 = "logician 2"
logician3 = "logician 3"

igor_is_sane, igor_is_human :: ProbeID
igor_is_sane = "Igor is sane"
igor_is_human = "Igor is human"

-- | A logician knows Igor if he knows his nature.
knows_igor l = agent l $ kTest $
     (l `knows_hat` igor_is_sane)
  /\ (l `knows_hat` igor_is_human)

-- | Igor tells the truth iff he is a sane human or insane vampire.
igor_tells_truthA = proc s ->
    ((igor_is_saneA -< s) `andAC` (igor_is_humanA -< s))
  `orAC`
    ((igor_is_insaneA -< s) `andAC` (igor_is_vampiricA -< s))

{-

As the logicians' questions are all independent, they can simply be
modelled as constraints on the initial states. In other words, this
puzzle has no temporal dimension.

-}

top = proc () ->
  do -- All states are initially plausible.
     s <- nondetLatchAC trueA -< ()

     probeA igor_is_sane <<< igor_is_saneA -< s
     probeA igor_is_human <<< igor_is_humanA -< s

     igor_tells_truth <- igor_tells_truthA -< s

     -- 1: Igor is a sane human?
     a1 <- (returnA -< igor_tells_truth)
             `iffAC` ((igor_is_saneA -< s) `andAC` (igor_is_humanA -< s))
     l1_out <- knows_igor logician1 -< a1

     -- 2: Igor is a sane vampire?
     a2 <- (returnA -< igor_tells_truth)
             `iffAC` ((igor_is_saneA -< s) `andAC` (igor_is_vampiricA -< s))
     l2_out <- knows_igor logician2 -< a2

     -- 3: Igor is an insane vampire?
     a3 <- (returnA -< igor_tells_truth)
             `iffAC` ((igor_is_insaneA -< s) `andAC` (igor_is_vampiricA -< s))
     l3_out <- knows_igor logician3 -< a3

     returnA -< (l1_out, l2_out, l3_out)

-------------------------------------------------------------------
-- Synthesis and model checking.
-------------------------------------------------------------------

-- FIXME singleSPRSynth should work too.
Just (kautos, m, (l1_out, l2_out, l3_out)) = clockSynth MinNone top
ctlM = mkCTLModel m

-- We want the initial state(s) where the dialogue went to plan. Ergo
-- a witness to each of the logicians not knowing Igor's nature a
-- priori.
dialogue_result = showWitness ctlM (neg (prop l1_out) /\ neg (prop l2_out) /\ neg (prop l3_out))

test_mc = isOK (CTL.mc ctlM (ag ((neg (prop l1_out) /\ neg (prop l2_out) /\ neg (prop l3_out))
                             --> (probe igor_is_sane /\ neg (probe igor_is_human)))))
test_mc_non_trivial = not (isOK (CTL.mc ctlM (neg (neg (prop l1_out) /\ neg (prop l2_out) /\ neg (prop l3_out)))))

-- Answer: Igor is a sane vampire.
