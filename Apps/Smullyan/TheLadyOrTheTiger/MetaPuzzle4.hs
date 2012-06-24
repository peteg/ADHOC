{-# LANGUAGE Arrows, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, NoMonomorphismRestriction, RankNTypes, TypeFamilies, TypeOperators, UndecidableInstances #-}
{- A puzzle from Raymond Smullyan's "The Lady or the Tiger?", OUP, 1982.
 - Copyright   :  (C)opyright 2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -
 - ghc -Wall -O -main-is MetaPuzzle4.main -rtsopts -prof -package ADHOC MetaPuzzle4.hs
 - ghci -package ADHOC MetaPuzzle4.hs
 -
 -}
module MetaPuzzle4 where

-------------------------------------------------------------------
-- Dependencies
-------------------------------------------------------------------

import Prelude hiding ( id, (.) )

-- FIXME ADHOC needs to export this
import Text.PrettyPrint hiding ( Mode )
import qualified Text.PrettyPrint as PP

import ADHOC
import ADHOC.Internals ( cbool2bdd )
import ADHOC.NonDet

import ADHOC.ModelChecker.CTL as CTL
import ADHOC.ModelChecker.CounterExamples

import ADHOC.Knowledge

-------------------------------------------------------------------
-- The puzzle.
-------------------------------------------------------------------

{-

p93:

4. Knights, Knaves and Normals

One the island of Knights, Knaves and Normals, knights always tell the
truth, knaves always lie, and those called /normal/ can either lie or
tell the truth (and sometimes one and sometimes the other).

One day I visited this island and met two inhabitants, A and B. I
already knew that one of them was a knight and the other was normal,
but I didn't know which was which. I asked A whether B was normal, and
he answered me, either yes or no. I then knew which was which.

Which of the two is normal?

-}

-------------------------------------------------------------------
-- The type of inhabitants.
-- This is not necessary as there is no knave in the story.
-------------------------------------------------------------------

-- | An inhabitant is either a knight, a knave or normal.
newtype Inhabitant b = Inhabitant { unInhabitant :: (b, b) }

instance (Zero (~>) b) => Zero (~>) (Inhabitant b) where
  zeroA = zeroA >>> arr Inhabitant

instance Structure b (Inhabitant b) where
  type SIwidth b (Inhabitant b) = Two
  structure = StateM (\(x : y : zs) -> (Inhabitant (x, y), zs))

instance StructureDest b (Inhabitant b) where
  destructure = (unInhabitant >>> arr (\(x, y) -> [x, y]))

-- FIXME this is a big violation of abstraction.
-- Can we write instances in terms of CBool and have them translated into BDDs?
instance RenderInState (Inhabitant CBool) BDD where
    renderInState (Inhabitant (v0, v1)) = RenderFn (PP.text . f)
      where
        f s | u0 == false && u1 == false = "Knight"
            | u0 == false && u1 /= false = "Knave"
            | u0 /= false && u1 == false = "Normal"
            | otherwise = error "Inhabitant.renderInState: FIXME something's wrong."
          where (u0, u1) = (cbool2bdd v0 /\ s, cbool2bdd v1 /\ s)

isKnightA :: ArrowComb (~>) => Inhabitant (B (~>)) ~> B (~>)
isKnightA = arr unInhabitant >>> notA *** notA >>> andA

isKnaveA :: ArrowComb (~>) => Inhabitant (B (~>)) ~> B (~>)
isKnaveA = arr unInhabitant >>> notA *** id >>> andA

isNormalA :: ArrowComb (~>) => Inhabitant (B (~>)) ~> B (~>)
isNormalA = arr unInhabitant >>> id *** notA >>> andA

validInhabitantA :: ArrowComb (~>) => Inhabitant (B (~>)) ~> B (~>)
validInhabitantA = isKnightA `orAC` isKnaveA `orAC` isNormalA

-------------------------------------------------------------------

-- | State: the type of A and B.
type State b = (Inhabitant b, Inhabitant b)

inhabitant_a, inhabitant_b :: State b -> Inhabitant b
inhabitant_a = fst
inhabitant_b = snd

smullyan :: AgentID
smullyan = "Smullyan"

a_is_normal, b_is_normal :: ProbeID
a_is_normal = "A is normal"
b_is_normal = "B is normal"

{-

There is no temporal dimension here.

-}

smullyan_knowsA = agent smullyan $ kTest $
     (smullyan `knows_hat` a_is_normal)
  /\ (smullyan `knows_hat` b_is_normal)

top = proc () ->
  do -- One is a knight and the other is normal.
     s <- (| nondetLatchAC
                   (\s -> ((isKnightA -< inhabitant_a s) `andAC` (isNormalA -< inhabitant_b s))
                         `orAC`
                           ((isNormalA -< inhabitant_a s) `andAC` (isKnightA -< inhabitant_b s)) ) |)

     probeA a_is_normal <<< isNormalA -< inhabitant_a s
     probeA b_is_normal <<< isNormalA -< inhabitant_b s

     -- A normal is non-deterministic, so A tells the truth either
     -- always or whenever. FIXME the formulation here only works for
     -- knights and normals, not all three types.
     a_tells_the_truth <- (isKnightA -< inhabitant_a s) `orAC` (nondetBitA -< ())

     -- "I asked A whether B was normal, and he answered me, either
     -- yes or no. I then knew which was which."
     a <- (returnA -< a_tells_the_truth)
            `iffAC` (isNormalA -< inhabitant_b s)

     smullyan_knowsA -< a

-------------------------------------------------------------------
-- Synthesis and model checking.
-------------------------------------------------------------------

-- FIXME singleSPRSynth should work too.
Just (kautos, m, out) = clockSynth MinNone top
ctlM = mkCTLModel m

-- We want the initial state(s) where the dialogue went to plan. Ergo
-- a witness to Smullyan knowing which of A and B are normal.
dialogue_result = showWitness ctlM (prop out)
test_mc = isOK (CTL.mc ctlM (prop out --> probe a_is_normal))
test_mc_non_trivial = not (isOK (CTL.mc ctlM (neg (prop out))))
test_mc_canonical = isOK (CTL.mc ctlM (ag (prop out --> probe a_is_normal)))

-- Answer: A is normal.
