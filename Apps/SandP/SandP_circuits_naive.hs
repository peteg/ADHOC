{-# LANGUAGE Arrows, FlexibleContexts, NoMonomorphismRestriction, RankNTypes, TypeOperators #-}
{-   The Mr S(um) and Mr P(roduct) puzzle analysed by McCarthy, and van
 -   Ditmarsch, Ruan, Verbrugge.
 - Copyright   :  (C)opyright 2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -
 - ghc -O -main-is Main.main -rtsopts -prof -package ADHOC SandP_circuits_naive.hs
 - ghci -package ADHOC SandP_circuits_naive.hs
 -

BDDs blow up on multipliers. Thus we need to take a lot of care to get
something that converges.

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

import Prelude hiding ( id, product, sum )
import Data.List	( foldl', genericLength )

import ADHOC hiding ( sum, product )
import ADHOC.Data.Arithmetic
import ADHOC.NonDet
import ADHOC.Patterns	( conjoinA, mapAC )

import ADHOC.Knowledge

import ADHOC.ModelChecker.CTL as CTL
import ADHOC.ModelChecker.CounterExamples

-------------------------------------------------------------------
-- The state of the dialogue.
-------------------------------------------------------------------

-- This model is low-level, just to show we can solve the puzzle.
type State (~>) = Nat Two (~>)

-- Choose between four arrows, depending on what state we're in.
-- Naive.
seq4A :: forall env b (~>).
             (ArrowLoop (~>), ArrowEq (~>) (State (~>)), ArrowNum (~>) (State (~>)), ArrowMux (~>) b, ArrowDelay (~>) (State (~>)))
          => (env ~> b) -> (env ~> b) -> (env ~> b) -> (env ~> b) -> (env ~> b)
seq4A init f g h = proc env ->
  do rec s <- (| delayAC (nat (undefined :: Two) <<< fromIntegerA 0 -< ()) (inc -< s) |)
     c0 <- (| eqAC (returnA -< s) (fromIntegerA 0 -< ()) |)
     c1 <- (| eqAC (returnA -< s) (fromIntegerA 1 -< ()) |)
     c2 <- (| eqAC (returnA -< s) (fromIntegerA 2 -< ()) |)
     (| muxAC (returnA -< c0)
         (init -< env)
         (| muxAC (returnA -< c1)
             (f -< env)
             (| muxAC (returnA -< c2)
                 (g -< env)
                 (h -< env) |) |) |)

-------------------------------------------------------------------
-- The scenario.
-------------------------------------------------------------------

mrS :: AgentID
mrS = "Mr. S."

mrP :: AgentID
mrP = "Mr. P."

mvar, nvar :: String
mvar = "m"
nvar = "n"

-- | An agent knows the two values.
agent_knows :: AgentID -> KF
agent_knows aid = aid `knows_hat` mvar /\ aid `knows_hat` nvar

{-
Mr. P: I don’t know the numbers.
Mr. S: I knew you didn’t know. I don’t know either.
Mr. P: Now I know the numbers.
Mr. S: Now I know them too.
-}

mrP_rec = proc _ ->
  do k <- kbpTest (agent_knows mrP) -< ()
     (| seq4A
         (notA -< k) -- "I don't know the numbers"
         (trueA -< ()) -- pause
         (returnA -< k) -- "Now I know the numbers"
         (trueA -< ()) -- pause
      |)

mrS_rec = proc _ ->
  do k <- kbpTest (agent_knows mrS) -< ()
     kk <- kbpTest (mrS `knows` neg (agent_knows mrP)) -< ()
     -- "I knew you didn't know"
     dkk <- (| delayAC (falseA -< ()) (returnA -< kk) |)
     (| seq4A
         (trueA -< ()) -- pause
         ( (returnA -< dkk) `andAC` (notA -< k) ) -- "I knew you didn't know. I don't know either."
         (trueA -< ()) -- pause
         (returnA -< k) -- "Now I know them too."
      |)

-- | Initially Mr. S is told their sum and Mr. P is told their product.
agent_arrs = mkSizedListA
  [ (mrS, numCastA <<< addA, mrS_rec)
  , (mrP, mulA,              mrP_rec) ]
      `withLength` (undefined :: Two)

top = proc () ->
  do mn <- (| nondetLatchAC (\(m, n) ->
                 ((fromIntegerA 2 -< ()) `leAC` (nat (undefined :: Seven) -< m))
         `andAC` ((returnA -< m) `leAC` (returnA -< n))
         `andAC` ((returnA -< n) `leAC` (fromIntegerA 99 -< ()))) |)
     probeA mvar *** probeA nvar -< mn
     rec acts <- (| delayAC (replicateSL <<< falseA -< ())
                            (| (broadcast agent_arrs)
                                  (returnA -< mn)
                                  (returnA -< acts) |) |)

     returnA -< acts

-------------------------------------------------------------------
-- Synthesis and model checking.
-------------------------------------------------------------------

Just (m, outputs)
  = isConstructive top

-- Synthesis using the SPR semantics
(kautos, m') = broadcastSprSynth m

ctlM = mkCTLModel m'
[mrS_out, mrP_out] = unSizedListA outputs

-- We want the initial state(s) where the dialogue went to plan.
-- This is where all (four of) the announcements came out true.
dialogue_result = showWitness ctlM (ex (ex (p /\ ex (p /\ ex (p /\ ex p)))))
  where p = prop mrS_out /\ prop mrP_out

-- | This example is big enough that we need to compile it...  It
-- seems that ReorderStableWindow3 is faster than ReorderSift.
main :: IO ()
main =
  do dynamicReordering ReorderStableWindow3 -- ReorderSift -- ReorderStableWindow3
     -- print m
     -- print test_dialogue
     dot kautos
     dialogue_result
