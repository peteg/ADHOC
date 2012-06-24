{-# LANGUAGE Arrows, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, NoMonomorphismRestriction, RankNTypes, TypeOperators, TypeFamilies, UndecidableInstances #-}
{- A puzzle from Raymond Smullyan's "The Lady or the Tiger?", OUP, 1982.
 - Copyright   :  (C)opyright 2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -
 - ghc -Wall -O -main-is MetaPuzzle5.main -rtsopts -prof -package ADHOC MetaPuzzle5.hs
 - ghci -package ADHOC MetaPuzzle5.hs
 -
 -}
module MetaPuzzle5 where

-------------------------------------------------------------------
-- Dependencies
-------------------------------------------------------------------

import Prelude hiding ( id, (.), mapM )

-- FIXME ADHOC needs to export this
import Text.PrettyPrint hiding ( Mode )
import qualified Text.PrettyPrint as PP

import ADHOC
import ADHOC.Internals	( cbool2bdd ) -- FIXME unsafe
import ADHOC.NonDet

import ADHOC.ModelChecker.CTL as CTL
import ADHOC.ModelChecker.CounterExamples

import ADHOC.Knowledge

-------------------------------------------------------------------
-- The puzzle.
-------------------------------------------------------------------

{-

p94:

5. Who is the Spy?

Now we come to a far more intricate metapuzzle!

This case involves a trial of three defendants: A, B, and C. It was
known at the outset of the trial that one of the three was a knight
(he always told the truth), one a knave (he always lied), and the
other was a /spy/ who was normal (he sometimes lied and sometimes told
the truth). The purpose of the trial was to find the spy.

First, A was asked to make a statement. He said either that C is a
knave or that C was the spy, but we are not told which. Then B said
either that A is a knight, or that A is a knave, or that A was the
spy, but we are not told which. Then C made a statement about B, and
he said either that B was a knight, or that B was a knave, or that B
was the spy, but we are not told which. The judge then knew who the
spy was and convicted him.

This case was described to a logician, who worked on the problem for a
while, and then said "I do not have enough information to know which
one is the spy." The logician was then told what A said, and he then
figured out who the spy was.

Which one is the spy -- A, B, or C?

-}

-------------------------------------------------------------------
-- We need two types with three elements.
--
-- We use this one to represent which of three statements a defendant
-- made.
-------------------------------------------------------------------

newtype ThreeElts b = ThreeElts { unThreeElts :: (b, b) }

instance (Zero (~>) b) => Zero (~>) (ThreeElts b) where
  zeroA = zeroA >>> arr (\z -> ThreeElts (z, z))

instance StructureDest b (ThreeElts b) where
  destructure = (unThreeElts >>> arr (\(x, y) -> [x, y]))

instance Structure b (ThreeElts b) where
  type SIwidth b (ThreeElts b) = Two
  structure = StateM (\(x : y : zs) -> (ThreeElts (x, y), zs))

-- FIXME this is a big violation of abstraction.
-- Can we write instances in terms of CBool and have them translated into BDDs?
instance RenderInState (ThreeElts CBool) BDD where
    renderInState (ThreeElts (v0, v1)) = RenderFn (PP.text . f)
      where
        f s | u0 == false && u1 == false = "Zero"
            | u0 == false && u1 /= false = "One"
            | u0 /= false && u1 == false = "Two"
            | otherwise = error "ThreeElts.renderInState: FIXME something's wrong."
          where (u0, u1) = (cbool2bdd v0 /\ s, cbool2bdd v1 /\ s)

isZeroA :: ArrowComb (~>) => ThreeElts (B (~>)) ~> B (~>)
isZeroA = arr unThreeElts >>> notA *** notA >>> andA

isOneA :: ArrowComb (~>) => ThreeElts (B (~>)) ~> B (~>)
isOneA = arr unThreeElts >>> notA *** id >>> andA

isTwoA :: ArrowComb (~>) => ThreeElts (B (~>)) ~> B (~>)
isTwoA = arr unThreeElts >>> id *** notA >>> andA

validThreeEltsA :: ArrowComb (~>) => ThreeElts (B (~>)) ~> B (~>)
validThreeEltsA = isZeroA `orAC` isOneA `orAC` isTwoA

threeEltsCaseAC varr f g h = proc env ->
  do v <- varr -< env
     (| muxAC (isZeroA -< v)
              (f -< env)
              (| muxAC (isOneA -< v)
                   (g -< env)
                   (h -< env) |) |)

-------------------------------------------------------------------
-- The type of inhabitants.
-------------------------------------------------------------------

newtype Inhabitant b = Inhabitant { unInhabitant :: ThreeElts b }

instance (Zero (~>) b) => Zero (~>) (Inhabitant b) where
  zeroA = zeroA >>> arr Inhabitant

instance Structure b (Inhabitant b) where
  type SIwidth b (Inhabitant b) = SIwidth b (ThreeElts b)
  structure = fmap Inhabitant structure

instance StructureDest b (Inhabitant b) where
  destructure = (unInhabitant >>> destructure)

instance RenderInState (Inhabitant CBool) BDD where
    renderInState = renderInState . unInhabitant

isKnightA :: ArrowComb (~>) => Inhabitant (B (~>)) ~> B (~>)
isKnightA = arr unInhabitant >>> isZeroA

isKnaveA :: ArrowComb (~>) => Inhabitant (B (~>)) ~> B (~>)
isKnaveA = arr unInhabitant >>> isOneA

isNormalA :: ArrowComb (~>) => Inhabitant (B (~>)) ~> B (~>)
isNormalA = arr unInhabitant >>> isTwoA

-- | We are told that the spy is normal.
isSpyA :: ArrowComb (~>) => Inhabitant (B (~>)) ~> B (~>)
isSpyA = isNormalA

validInhabitantA :: ArrowComb (~>) => Inhabitant (B (~>)) ~> B (~>)
validInhabitantA = arr unInhabitant >>> validThreeEltsA

inhabitantCaseAC varr f g h = threeEltsCaseAC (varr >>> arr unInhabitant) f g h

-------------------------------------------------------------------

-- The system state.

-- ((Type of A, which statement A made)
--- (Type of B, which statement B made)
--  (Type of C, which statement C made))
type State b =
  ((Inhabitant b, b),
   (Inhabitant b, ThreeElts b),
   (Inhabitant b, ThreeElts b))

-- | Project the inhabitants' type from the state.
a, b, c :: State b -> Inhabitant b
a (x, _, _) = fst x
b (_, x, _) = fst x
c (_, _, x) = fst x

-- | Project the habitants' statement from the state.
s_a :: State b -> b
s_b, s_c :: State b -> ThreeElts b
s_a (x, _, _) = snd x
s_b (_, x, _) = snd x
s_c (_, _, x) = snd x

judge, logician :: AgentID
judge = "judge"
logician = "logician"

a_is_the_spy, b_is_the_spy, c_is_the_spy :: ProbeID
a_is_the_spy = "A is the spy"
b_is_the_spy = "B is the spy"
c_is_the_spy = "C is the spy"

a_said_c_is_a_knave = "A said that C is a knave"

-- | The constraint on the defendants:
--      /This case involves a trial of three defendants: A, B, and
--      C. It was known at the outset of the trial that one of the
--      three was a knight (he always told the truth), one a knave (he
--      always lied), and the other was a /spy/ who was normal (he
--      sometimes lied and sometimes told the truth). The purpose of
--      the trial was to find the spy./
defendants = proc s ->
    -- All are valid inhabitants.
    (validInhabitantA -< a s) `andAC` (validInhabitantA -< b s) `andAC` (validInhabitantA -< c s)
  `andAC`
    -- One is a knight.
    ((isKnightA -< a s) `orAC` (isKnightA -< b s) `orAC` (isKnightA -< c s))
  `andAC`
    -- One is a knave.
    ((isKnaveA -< a s) `orAC` (isKnaveA -< b s) `orAC` (isKnaveA -< c s))
  `andAC`
    -- One is normal.
    ((isNormalA -< a s) `orAC` (isNormalA -< b s) `orAC` (isNormalA -< c s))

-- | A defendant tells the truth if he is a knight, and sometimes if
-- he is normal. He lies if he is a knave, and sometimes if he is
-- normal.
agent_says d starr = proc s ->
  do st <- starr -< s
     (| inhabitantCaseAC (returnA -< d s)
          (returnA -< st) -- Knight
          (notA -< st) -- Knave
          (trueA -< ()) -- Normal
      |)

-- | Statements by the defendants.
statements = proc s ->
     (validThreeEltsA -< s_b s) `andAC` (validThreeEltsA -< s_c s)
   `andAC`

     -- First, A was asked to make a statement. He said either that C
     -- is a knave or that C was the spy, but we are not told which.
     (| (agent_says a)
          (| muxAC (returnA -< s_a s)
               (isKnaveA -< c s)
               (isSpyA -< c s) |) |)
   `andAC`

     -- Then B said either that A is a knight, or that A is a knave,
     -- or that A was the spy, but we are not told which.
     (| (agent_says b)
          (| threeEltsCaseAC (returnA -< s_b s)
               (isKnightA -< a s)
               (isKnaveA -< a s)
               (isSpyA -< a s) |) |)

   `andAC`

     -- Then C made a statement about B, and he said either that B was
     -- a knight, or that B was a knave, or that B was the spy, but we
     -- are not told which.
      (| (agent_says c)
           (| threeEltsCaseAC (returnA -< s_c s)
                (isKnightA -< b s)
                (isKnaveA -< b s)
                (isSpyA -< b s) |) |)

-- | An agent knows who the spy is. As there is exactly one spy, this
-- is enough.
agent_knows l =
     (l `knows` probe a_is_the_spy)
  \/ (l `knows` probe b_is_the_spy)
  \/ (l `knows` probe c_is_the_spy)

-- | The judge's behaviour:
--      The judge then knew who the spy was and convicted him.
-- FIXME I don't think we care about the judge's behaviour.
judgeA = agent judge $ kTest $ agent_knows judge

-- | The logician's behaviour:
--      This case was described to a logician, who worked on the
--      problem for a while, and then said "I do not have enough
--      information to know which one is the spy." The logician was
--      then told what A said, and he then figured out who the spy
--      was.
logicianA = agent logician $ kTest $ agent_knows logician

top = proc () ->
  do s <- (| nondetLatchAC
               (\s -> (defendants -< s) `andAC` (statements -< s)) |)

     probeA a_is_the_spy <<< isSpyA -< a s
     probeA b_is_the_spy <<< isSpyA -< b s
     probeA c_is_the_spy <<< isSpyA -< c s

     -- The judge heard which statements were made.
     -- We're only interested in the states where the judge knows who the Spy is.
     jout <- judgeA -< (s_a s, s_b s, s_c s)

     -- The logician initially doesn't know who the spy is, but does
     -- when told A's statement.
     -- FIXME we need to delay an instant so that the judge's conviction can be propagated.
     -- Think about nicer ways to say this.
     lin <- (| delayAC (zeroA -< ()) (returnA -< jout) |)
        &&& (| muxAC (isInitialState -< ())
                 (zeroA -< ())
                 (returnA -< s_a s) |)

     lout <- logicianA -< lin

     -- Auxiliary probes.
     probeA a_said_c_is_a_knave -< s_a s

     returnA -< (jout, lout)

-------------------------------------------------------------------
-- Synthesis and model checking.
-------------------------------------------------------------------

-- Need to redo the scenario using a broadcast combinator.
-- Just (kautps, m, (jout, lout)) = broadcastSprSynth MinNone top

Just (kautps, m, (jout, lout)) = clockSynth MinNone top
ctlM = mkCTLModel m

-- Smullyan, first fork: if the judge knows who the spy is, and A said
-- that C is a Knave, then the spy is B.
test_mc_judge_first_fork = isOK (CTL.mc ctlM (prop jout /\ probe a_said_c_is_a_knave --> probe b_is_the_spy))
mc_judge_first_fork_witness = showWitness ctlM (prop jout /\ probe a_said_c_is_a_knave)
-- Check the antecedent isn't trivial.
test_judge_first_fork_non_trivial = not (isOK (CTL.mc ctlM (neg (prop jout /\ probe a_said_c_is_a_knave))))

-- Sanity: The judge doesn't always convict B.
test_mc_sanity_judge_not_always_b = not (isOK (CTL.mc ctlM (prop jout --> probe b_is_the_spy)))

-- Smullyan, second fork: in fact the judge sometimes convicts each of
-- A, B and C if A said that C is the spy.
test_mc_judge_second_fork_a = not (isOK (CTL.mc ctlM (prop jout /\ neg (probe a_said_c_is_a_knave) --> neg (probe a_is_the_spy))))
test_mc_judge_second_fork_b = not (isOK (CTL.mc ctlM (prop jout /\ neg (probe a_said_c_is_a_knave) --> neg (probe b_is_the_spy))))
test_mc_judge_second_fork_c = not (isOK (CTL.mc ctlM (prop jout /\ neg (probe a_said_c_is_a_knave) --> neg (probe c_is_the_spy))))
test_judge_second_fork_non_trivial = not (isOK (CTL.mc ctlM (neg (prop jout /\ neg (probe a_said_c_is_a_knave)))))

mc_judge_second_fork_witness = showWitness ctlM (prop jout /\ neg (probe a_said_c_is_a_knave))

-- Therefore we conclude that B is the spy, as the judge convicted
-- someone and the logician (Smullyan) figured out who by this
-- reasoning.

-- However we really want the model checker to tell us directly.

-- Initially the logician doesn't know who was convicted.
test_mc_logician_initially_does_not_know = isOK (CTL.mc ctlM (neg (prop lout)))

-- After seeing that the judge convicts and what A said:
--  - he does know in the case that A said A said that C is a Knave.
test_mc_logician_first_fork_knows = isOK (CTL.mc ctlM (prop jout /\ probe a_said_c_is_a_knave --> ex (prop lout)))
--  - he does not know in the case that A said A said that C is the spy.
test_mc_logician_first_fork_does_not_know = isOK (CTL.mc ctlM (neg (prop jout) /\ probe a_said_c_is_a_knave --> ex (neg (prop lout))))

-- The solution is canonical: when he knows, the spy is B.
test_mc_logician_canonical = isOK (CTL.mc ctlM (ex (prop lout) --> probe b_is_the_spy))

-- This gives us that B is the spy directly.
dialogue_result = showWitness ctlM (prop jout /\ neg (prop lout) /\ ex (prop lout))
