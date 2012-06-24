{- Basic epistemic model checking.
 - Copyright   :  (C)opyright 2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -}
module ADHOC.ModelChecker.Knowledge
    (
      kobs
    ) where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude hiding ( id, (.) )

import ADHOC.Basis
import ADHOC.Model
import ADHOC.ModelChecker.CTL

-------------------------------------------------------------------
-- Observational semantics.
-------------------------------------------------------------------

{-

The observational semantics for knowledge simply partitions the
reachable state space under the agent's observation function. We can
reduce this to a proposition, i.e. the set of states where the agent
knows the formula, without adding anything to the model.

zAs in MCK, we could mix CTL and K_obs modalities but we don't need
that for our examples.

-}

kobs :: BDDOps b => CTLModel b -> KF -> CTL b
kobs ctlM = CTLprop . propSat m kObsSem
  where
    m = ctlModel ctlM
    groupS = ctlGroupS ctlM
    subSforC = ctlSubSforC ctlM

    kss' = subSforC (ctlReachable ctlM)
    valEq bs = conjoin [ b <-> subSforC b | b <- bs ]

    obsEq aid =
      let Just (os, _aRenderObs) = aid `lookup` mAgents m
       in conjoin [ o <-> subSforC o | o <- os ]

    obssEq aids = transitiveClosure m $ disjoin (map obsEq aids)

    kObsSem = KSem
      { ksem = \aid fsat -> forall groupS ((kss' /\ obsEq aid) --> subSforC fsat)
      , khatsem = \aid bs -> forall groupS ((kss'  /\ obsEq aid) --> valEq bs)
      , cksem = \aids fsat -> forall groupS ((kss' /\ obssEq aids) --> subSforC fsat)
      , ckhatsem = \aids bs -> forall groupS ((kss' /\ obssEq aids) --> valEq bs)
      }
