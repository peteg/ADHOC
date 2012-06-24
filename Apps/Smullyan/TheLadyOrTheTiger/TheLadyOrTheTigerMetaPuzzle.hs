{-# LANGUAGE Arrows, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, NoMonomorphismRestriction, RankNTypes, TypeFamilies, TypeOperators, UndecidableInstances #-}
{- A puzzle from Raymond Smullyan's "The Lady or the Tiger?", OUP, 1982.
 - Copyright   :  (C)opyright 2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -
 - ghc -Wall -O -main-is TheLadyOrTheTiger.main -rtsopts -prof -package ADHOC TheLadyOrTheTiger.hs
 - ghci -package ADHOC TheLadyOrTheTiger.hs
 -
 -}
module TheLadyOrTheTigerMetaPuzzle where

-------------------------------------------------------------------
-- Dependencies
-------------------------------------------------------------------

import Prelude hiding ( id, (.) )

-- FIXME ADHOC needs to export this
import Text.PrettyPrint hiding ( Mode )
import qualified Text.PrettyPrint as PP

import ADHOC
import ADHOC.Internals		( cbool2bdd )
import ADHOC.NonDet

import ADHOC.Data.Arithmetic

import ADHOC.ModelChecker.CTL
import ADHOC.ModelChecker.CounterExamples

import ADHOC.Knowledge

-------------------------------------------------------------------
-- The type of room inhabitants.
-------------------------------------------------------------------

-- | A room is either empty, or contains a lady or a tiger.
newtype RoomContents b = RoomContents { unRoomContents :: (b, b) }

instance (Zero (~>) b) => Zero (~>) (RoomContents b) where
    zeroA = zeroA >>> arr (\z -> RoomContents (z, z))

instance Structure b (RoomContents b) where
  type SIwidth b (RoomContents b) = Two
  structure = StateM (\(x : y : zs) -> (RoomContents (x, y), zs))

instance StructureDest b (RoomContents b) where
    destructure = (unRoomContents >>> arr (\(x, y) -> [x, y]))

instance RenderInState (RoomContents CBool) BDD where
    renderInState (RoomContents (v0, v1)) = RenderFn (PP.text . f)
      where
        f s | u0 == false && u1 == false = "Empty"
            | u0 == false && u1 /= false = "Lady"
            | u0 /= false && u1 == false = "Tiger"
            | otherwise = error "RoomContents.renderInState: FIXME something's wrong."
          where (u0, u1) = (cbool2bdd v0 /\ s, cbool2bdd v1 /\ s)

-- | A room is empty if both bits are false.
isEmptyA :: ArrowComb (~>) => RoomContents (B (~>)) ~> B (~>)
isEmptyA = arr unRoomContents >>> notA *** notA >>> andA

hasLadyA :: ArrowComb (~>) => RoomContents (B (~>)) ~> B (~>)
hasLadyA = arr unRoomContents >>> notA *** id >>> andA

hasTigerA :: ArrowComb (~>) => RoomContents (B (~>)) ~> B (~>)
hasTigerA = arr unRoomContents >>> id *** notA >>> andA

validRoomA :: ArrowComb (~>) => RoomContents (B (~>)) ~> B (~>)
validRoomA = isEmptyA ∨ hasLadyA ∨ hasTigerA

-------------------------------------------------------------------
-- Types
-------------------------------------------------------------------

type NineRooms (~>) = SizedList Nine (RoomContents (B (~>)))

type NineStatements (~>) = SizedList Nine (B (~>))

-------------------------------------------------------------------
-- The puzzle.
-------------------------------------------------------------------

{-

p22:

The Fourth Day

"Horrible!" said the king. "It seems I can't make my puzzles hard
enough to trap these fellows! Well, we have only one more trial to go,
but this time I'll /really/ give the prisoner a run for his money!"

Puzzle 12. A logical labyrinth.

Well, the king was as good as his word. Instead of having three rooms
for the prisoner to choose from, he gave him nine! As he explained,
only one room contained a lady; each of the other eight either
contained a tiger or was empty. And, the king added, the sign on the
door of the room containing the lady is true; the signs on doors of
all rooms containing tigers are false; and the signs on doors of empty
rooms can be either true or false.

-}

constraints :: ArrowComb (~>) => (NineRooms (~>), NineStatements (~>)) ~> B (~>)
constraints = proc (rs, ss) ->
     -- Each room contained a lady or a tiger, or was empty.
     (conjoinSL <<< mapSL validRoomA -< rs)
  ∧  -- Exactly one room contained a lady.
     (isOneHotSL <<< mapSL hasLadyA -< rs)
  ∧  -- The sign on the door of the room containing the lady is true.
     (conjoinSL <<< zipWithSL (hasLadyA *** id >>> impA) -< (rs, ss))
  ∧  -- The signs on doors of all rooms containing tigers are false.
      (conjoinSL <<< zipWithSL (hasTigerA *** notA >>> impA) -< (rs, ss))
     -- The signs on doors of empty rooms can be either true or false.

{-

Here are the signs:

-}

signs :: ArrowComb (~>) => (NineRooms (~>), NineStatements (~>)) ~> B (~>)
signs = proc (rs, ss) ->
  do let [r1, r2, r3, r4, r5, r6, r7, r8, r9] = unSizedListA rs
         [s1, s2, s3, s4, s5, s6, s7, s8, s9] = unSizedListA ss
     -- Room 1: "The Lady is in an odd-numbered room."
     ((returnA -< s1) ⟺ ((hasLadyA -< r1)
                       ∨ (hasLadyA -< r3)
                       ∨ (hasLadyA -< r5)
                       ∨ (hasLadyA -< r7)
                       ∨ (hasLadyA -< r9)))
      ∧  -- Room 2: "This room is empty."
          ((returnA -< s2) ⟺ (isEmptyA -< r2))
      ∧  -- Room 3: "Either sign V is right or sign VII is wrong."
          ((returnA -< s3) ⟺ ((returnA -< s5) ∨ (notA -< s7)))
      ∧  -- Room 4: "Sign I is wrong."
          ((returnA -< s4) ⟺ (notA -< s1))
      ∧  -- Room 5: "Either sign II or sign IV is right."
          ((returnA -< s5) ⟺ ((returnA -< s2) ∨ (returnA -< s4)))
      ∧  -- Room 6: "Sign III is wrong."
          ((returnA -< s6) ⟺ (notA -< s3))
      ∧  -- Room 7: "The Lady is not in room I."
          ((returnA -< s7) ⟺ (notA <<< hasLadyA -< r1))
      ∧  -- Room 8: "This room contains a Tiger and Room IX is Empty."
          ((returnA -< s8) ⟺ ((hasTigerA -< r8) ∧ (isEmptyA -< r9)))
      ∧  -- Room 9: "This room contains a Tiger and VI is wrong."
          ((returnA -< s9) ⟺ ((hasTigerA -< r9) ∧ (notA -< s6)))

{-

The prisoner studied the situation for a long while.

"The problem is not solvable!" he exclaimed angrily. "That's not
fair!"

"I know," laughed the king.

"Very funny!" replied the prisoner. "Come on, now, at least give me a
decent clue: is Room Eight empty or not?"

The king was decent enough to tell him whether VIII was empty or not,
and the prisoner was then able to deduce where the lady was.

Which room contained the lady?

-}

the_lady_is_in_room, room_is_empty :: Integer -> ProbeID
the_lady_is_in_room i = "the lady is in room " ++ show i
room_is_empty i = "room " ++ show i ++ " is empty"

room_prj :: Arrow (~>) => Int -> NineRooms (~>) ~> RoomContents (B (~>))
room_prj i = unSizedListA >>> arr (!! (i - 1))

-- | We only need one agent: the King sees everything and is
-- identified with the environment.
prisoner :: AgentID
prisoner = "Prisoner"

-- | The prisoner knows which room contains the lady.
prisoner_knows :: KF
prisoner_knows =
  disjoin [ prisoner `knows` probe (the_lady_is_in_room i) | i <- [ 1 .. 9 ] ]

prisonerA = agent prisoner $ kTest prisoner_knows

top = proc () ->
  do (rs, ss) <- (| nondetLatchAC
                      (\s -> (constraints -< s) ∧ (signs -< s))  |)

     -- Add the probes.
     mapSLn (\i -> probeA (the_lady_is_in_room i) <<< hasLadyA) -< rs
     probeA (room_is_empty 8) <<< isEmptyA <<< room_prj 8 -< rs

     -- Initially the prisoner doesn't know, but does when told
     -- whether Room Eight is empty or not.
     room8 <- (| delayAC (zeroA -< ()) (isEmptyA <<< room_prj 8 -< rs) |)
     prisonerA -< room8

-------------------------------------------------------------------
-- Synthesis and model checking.
-------------------------------------------------------------------

Just (kautos, m, pout) = singleSPRSynth MinNone top
ctlM = mkCTLModel m

-- We want the initial state(s) where the dialogue went to plan.
--
-- That is, there is a run where the prisoner doesn't know where the
-- lady is in the first instant, but does in the second.
test_mc = not (isOK (mc ctlM (neg (neg (prop pout) /\ ex (prop pout)))))

-- There are also runs where the prisoner never learns.
test_mc_neg = not (isOK (mc ctlM (neg (prop pout) /\ ex (prop pout))))

-- i.e. both are possible. However... if the prisoner ever knows where
-- the lady is, then the lady is in room 7.
test_mc_canonical = isOK (mc ctlM (ag (prop pout --> probe (the_lady_is_in_room 7))))

-- The model checker can tell us this directly:
dialogue_result = showWitness ctlM (neg (prop pout) /\ ex (prop pout))
