{-# LANGUAGE Arrows, FlexibleContexts, NoMonomorphismRestriction, RankNTypes, ScopedTypeVariables, TypeOperators #-}
{- Model checking the dining cryptographers.
 - Copyright   :  (C)opyright 2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -
 - ghc -O -main-is Main.main -rtsopts -prof -auto-all -caf-all -package ADHOC DiningCryptographers_Large.hs
 -}
module Main ( main ) where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude hiding ( (.), id )

import ADHOC
import ADHOC.Data.Arithmetic
import ADHOC.NonDet
import ADHOC.Patterns

import ADHOC.Knowledge

import ADHOC.ModelChecker.CTL as CTL
import ADHOC.ModelChecker.Knowledge

-------------------------------------------------------------------
-- Scenario
-------------------------------------------------------------------

-- | Three cryptographers. FIXME ugly: we also need to say how wide
-- the arithmetic needs to be.
type NumAgents = Three
type ArithmeticWidth = Two

dcAgentName :: Integer -> AgentID
dcAgentName i = "dc" ++ show i

dcPaid :: Integer -> ProbeID
dcPaid i = "paid" ++ show i

nsaPaid :: ProbeID
nsaPaid = "The NSA paid"

-- | The agent observes whether or not she herself paid, the coin flip
-- to her left and the final broadcast.
dcAgent i = proc ((said, whoPaid), lCoin) ->
  do ia <- fromIntegerA i -< ()
     iPaid <- probeA (dcPaid i) <<< eqA -< (whoPaid, ia)
     agent (dcAgentName i) aArr -< (iPaid, lCoin, said)
  where
    aArr = proc (iPaid, lCoin, _said) ->
      do rCoin <- nondetBitA -< ()
         say <- xorA <<< second iffA -< (iPaid, (lCoin, rCoin))
         returnA -< (rCoin, say)

-- | We represent who paid with a natural, where the agents are
-- numbered /1 .. NumAgents/ -- hence the NSA is notionally agent 0.
env = proc () ->
  do paid <- (| nondetChooseAC (\v ->
                  do numAgents <- constNatA (undefined :: ArithmeticWidth) n -< ()
                     leA -< (v, numAgents)) |)
     probeA "paid" -< paid
     -- Track whether the NSA paid
     probeA nsaPaid <<< eqA <<< fromIntegerA 0 &&& id -< paid
     -- The dining cryptographers sit in a circle
     (| combLoop (\coin ->
                      do rec (coin', said) <- fanoutSL dcAgent -< ((said `withLength` (undefined :: NumAgents), paid), coin)
                         returnA -< ((), coin')) |)
  where n = c2num (undefined :: NumAgents) :: Integer

-------------------------------------------------------------------
-- Specifications
-------------------------------------------------------------------

Just (m, ()) = isConstructive env
ctlM = mkCTLModel m

paid i = probe (dcPaid i)

-- We pick on two agents: the NSA and the first cryptographer.
dc1 = dcAgentName 1
paid1 = paid 1
paidNSA = probe nsaPaid

-- The netlist should look OK.
test_netlist = dotNL "dc.dot" env >> return True

-- If dc1 paid, then he knows the scenario (knowledge axiom + model).
test_dc1_paid = isOK (mc ctlM (paid1 --> kobs ctlM (dc1 `knows_hat` "paid")))

-- If dc1 didn't pay, then he doesn't know who paid (not true).
test_dc1_not_paid = isFailure (mc ctlM (neg paid1 --> neg (kobs ctlM (dc1 `knows_hat` "paid"))))

-- Full specification: if dc1 didn't pay then he knows either that the NSA
-- paid or (dc2 or dc3 but not which).
test_full_spec =
  isOK (mc ctlM (neg paid1
             --> (kobs ctlM ((dc1 `knows` paidNSA)
                          \/ ((dc1 `knows` neg paidNSA)
                           /\ (neg (dc1 `knows_hat` "paid")))))))

main =
  do _ <- test_netlist
     mapM_ print [ test_dc1_paid, test_dc1_not_paid, test_full_spec ]
     return ()
