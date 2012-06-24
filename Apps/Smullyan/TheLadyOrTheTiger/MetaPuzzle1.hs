{-# LANGUAGE Arrows, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, NoMonomorphismRestriction, RankNTypes, TypeOperators, UndecidableInstances #-}
{- A puzzle from Raymond Smullyan's "The Lady or the Tiger?", OUP, 1982.
 - Copyright   :  (C)opyright 2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -
 - ghc -Wall -O -main-is MetaPuzzle1.main -rtsopts -prof -package ADHOC MetaPuzzle1.hs
 - ghci -package ADHOC MetaPuzzle1.hs
 -
 -}
module MetaPuzzle1 where

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

p91:

1. The Case of John

The case involved a judicial investigation of identical twins. It was
known that at least one of them never told the truth, but it was not
known which. One of the twins was named John, and he had committed a
crime. (John was not necessarily the one who always lied.) The purpose
of the investigation was to find out which one was John.

"Are you John?" the judge asked the first twin.

"Yes, I am," was the reply.

"Are you John?" the judge asked the second twin.

The second twin then answered either yes or no, and the judge then
knew which one was John.

Was John the first or second twin?

-}

{-

All this type stuff is incredibly weak, and GHC does a terrible job
with it.

Using newtypes implies the need for a bunch of (trivial) instances we
should be able to derive.

Trying to restrict types with B (~>) from ArrowComb leads to a world
of TypeFamilies pain: 'type' in ArrowComb is not injective, so we end
up with a bazillion arrows that are all really the same one, and no
easy way to say that.

-}


-- | A 'Person' is John iff the bit is true.
type Person b = b

isJohnA :: Arrow (~>) => Person (B (~>)) ~> B (~>)
isJohnA = id

-- The system state.
-- (Is person 1 John?, Is person2 John?, Is statement1 true?, Is statement2 true?, Did person2 say yes?)
-- FIXME no need to include answers in the state ??
type State b = (Person b, Person b, b, b, b)

p1, p2 :: State b -> Person b
s1, s2 :: State b -> b
a2 :: State b -> b
p1 (b, _, _, _, _) = b
p2 (_, b, _, _, _) = b
s1 (_, _, b, _, _) = b
s2 (_, _, _, b, _) = b
a2 (_, _, _, _, b) = b

judge :: AgentID
judge = "judge"

p1_is_john :: ProbeID
p1_is_john = "Person 1 is John"

top = proc () ->
  do state <- (| nondetLatchAC
                   (\s ->
                         -- Exactly one of the twins is John.
                         ((isJohnA -< p1 s) `xorAC` (isJohnA -< p2 s))
                      `andAC`
                         -- At least one of the statements is false.
                         ((notA -< s1 s) `orAC` (notA -< s2 s))
                      `andAC`
                         -- The first statement is true iff the first person is John.
                         ((returnA -< s1 s) `iffAC` (isJohnA -< p1 s))
                      `andAC`
                         -- The second statement is true iff (the second person said 'yes' and is in fact John).
                         ((returnA -< s2 s) `iffAC` ((returnA -< a2 s) `iffAC` (isJohnA -< p2 s))) ) |)

     probeA p1_is_john <<< isJohnA -< p1 state

     -- Based on the two statements, the judge can tell who John is.
     -- As one of the twins is John, this is the same as asking if the
     -- first person is or is not John.
     -- The judge can observe the second assertion (whose value we aren't told).
     jout <- agent judge (kTest $ judge `knows_hat` p1_is_john) -< a2 state
     returnA -< jout

-------------------------------------------------------------------
-- Synthesis and model checking.
-------------------------------------------------------------------

-- FIXME clock should work too.
Just (kautos, m, jout) = singleSPRSynth MinNone top
ctlM = mkCTLModel m

-- We want the initial state(s) where the dialogue went to plan. Ergo
-- a witness to the judge knowing who John is.
dialogue_result = showWitness ctlM (prop jout)

-- Whenever the judge knows who John is, John is the second twin.
test_mc = isOK (CTL.mc ctlM (ag (prop jout --> neg (probe p1_is_john))))
test_mc_non_trivial = not (isOK (CTL.mc ctlM (neg (prop jout))))

-- Answer: John is the second twin.
