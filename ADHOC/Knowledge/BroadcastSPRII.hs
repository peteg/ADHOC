{-# OPTIONS_GHC -fno-ignore-asserts #-}
{- Synthesis for multi-agent synchronous perfect recall with independent initialisation.
 - Copyright   :  (C)opyright 2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -
 - Synthesis for:
 -   - perfect recall in broadcast environments
 -   - multi-agent
 -   - agents and the environment are independently initialised (i.e. the agents' initial observations are empty)
 -   - atemporal
 -   - Explicit-state construction of a Moore-style automaton
 -
 - See the Isabelle theory for more details.
 -}
module ADHOC.Knowledge.BroadcastSPRII
    ( broadcastSprSynthII
    , broadcastSprSynthII'
    ) where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude hiding ( id, (.) )

import Control.Monad	( foldM, when )
import System.IO.Unsafe	( unsafePerformIO )

import Data.List	( foldl' )
import Data.Maybe	( fromMaybe, isNothing )

import ADHOC.Basis
import ADHOC.Constructivity ( isConstructive' )
import ADHOC.Model	( KF(..), KSem(..), propSat, Model(..), RenderFn, renderFn, transitiveClosure )

import ADHOC.Knowledge.ExplicitStateAutomata ( Hashable(..), Automaton, Synth )
import qualified ADHOC.Knowledge.ExplicitStateAutomata as Auto

-------------------------------------------------------------------

-- | States of the constructed automata.
--
-- Consists of a pair of relations between initial states and
-- final/current states. The first relation captures "what everyone
-- knows" and the second what a particular agent knows.
newtype SPRState = SPRState (BDD, BDD)
                   deriving (Eq, Ord, Show)

instance Hashable SPRState where
  hash (SPRState (x, y)) = hash (x, y)

type SPRAutomaton = Automaton BDD BDD SPRState

-------------------------------------------------------------------

-- | Synthesise automata that implement the knowledge conditionals.
broadcastSprSynthII :: Synth BDD SPRState c
broadcastSprSynthII minType = fmap synth . isConstructive' 0
  where
    synth (m, c)
      | isNothing (mCommonObs m) = error $ "FIXME broadcastSprSynth requires a common observation."
      | otherwise = unsafePerformIO $
          do putStrLn $ "broadcastSprSynth: constructing " ++ show (length (mKconds m)) ++ " automata..."
             automata0 <- mapM (mkAutomaton0 m) (mKconds m)
             putStrLn "broadcastSprSynth: minimising automata..."
             automata <- mapM (Auto.minimize minType) automata0
             putStrLn "broadcastSprSynth: adding automata to the model..."
             m' <- Auto.automata2model m automata
             putStrLn "broadcastSprSynth: done."
             return (automata, m', c)

-- | Synthesise automata that implement the knowledge conditionals.
--
-- This version computes one automaton at a time.
broadcastSprSynthII' :: Synth BDD SPRState c
broadcastSprSynthII' minType = fmap synth . isConstructive' 0 -- FIXME 1 temporary state vector for common knowledge testing
  where
    -- m0 is the original model, m is the one we're adding the
    -- automata to.
    mkA m0 m (i, kcond) = m `seq`
      do a0 <- mkAutomaton0 m0 kcond
         putStrLn "broadcastSprSynth: minimising automaton..."
         a <- Auto.minimize minType a0
         putStrLn "broadcastSprSynth: adding automata to the model..."
         m' <- Auto.toModel m (i, a)
         Auto.finished a
         return m'

    synth (m, c)
      | isNothing (mCommonObs m) = error $ "FIXME broadcastSprSynth requires a common observation."
      | otherwise = unsafePerformIO $
          do putStrLn $ "broadcastSprSynth: constructing " ++ show (length (mKconds m)) ++ " automata..."
             m' <- foldM (mkA m) m (zip [ 1 .. ] (mKconds m))
             m' `seq` putStrLn "broadcastSprSynth: done."
             return (error "broadcastSprSynthII': automata discarded", m', c)

----------------------------------------

-- | Context for the DFA construction.
--
-- To treat the relations, we need a set of temporary state variables
-- in addition to the current/next sets.
data Context b =
    Context
    { cGroupC :: Group b -- ^ Group the current-state variables
    , cGroupS :: Group b -- ^ Group the successor-state variables
    , cSubCforS :: b -> b
    , cSubSforC :: b -> b
    , cKSem :: b -> KSem b -- ^ Knowledge semantics for the given set of reachable states
    }

-- | Does the fixpoint and iteration over the frontier.
mkAutomaton0 :: Model BDD -> (AgentID, (KF, (BDD, BDD))) -> IO SPRAutomaton
mkAutomaton0 m = mkAutomaton m ctxt
  where
      -- Knowledge semantics: staged carefully.

      -- Map agents to their observational equality BDDs.
      -- Assumes we only have a few agents.
      obsEq aid0 =
          fromMaybe (error $ "BroadcastSPR.mkAutomata: unknown agent '" ++ aid0 ++ "'")
                    (aid0 `lookup` obsEq_map)
        where
          obsEq_map = [ (aid, map mkObs aObs)
                      | (aid, (aObs, _aRenderObs)) <- mAgents m ]
          mkObs o = (o <-> subSforC o)
    -- The observation on the initial and current/final states must be the same.
    -- FIXME reducing this to a single BDD here is too expensive. Can we use the partitioned transition relation ideas?
    --   I think so - but it probably won't help with the multiplier.

      obsEq' aid = conjoin (obsEq aid)

      -- for common knowledge
      cobsEq aids = transitiveClosure m $ disjoin (map obsEq' aids)

      -- Equal values in the final states.
      valEq bs = conjoin [ b <-> subSforC b | b <- bs ]

      -- Use rel_product rather than the obvious all /\ --> versions.
      -- "(all x. (P x /\ Q x) --> R x) == (not (exists x. P x /\ Q x /\ not R x))"
      -- FIXME update common knowledge too.
      sem nreachableStates = KSem
        { ksem = \aid fsat -> -- trace ("ksem: " ++ aid) $
            -- forall groupSTS ((subSTSforCT nreachableStates /\ obsEq' aid) --> subSTSforCT fsat)
            neg (rel_product groupS (subSforC nreachableStates /\ obsEq' aid) (neg (subSforC fsat)))
        , khatsem = \aid bs ->
            -- forall groupSTS ((subSTSforCT nreachableStates /\ obsEq' aid) --> valEq bs)
            neg (rel_product groupS (subSforC nreachableStates /\ obsEq' aid) (neg (valEq bs)))
        , cksem = \aids fsat ->
                   forall groupS ((subSforC nreachableStates /\ cobsEq aids) --> subSforC fsat)
        , ckhatsem = \aids bs ->
                   forall groupS ((subSforC nreachableStates /\ cobsEq aids) --> valEq bs)
        }

      groupS = cGroupS ctxt
      subSforC = cSubSforC ctxt

      ctxt = Context
           { cGroupC = mkGroup (mStateVars m)
           , cGroupS = mkGroup (mStateVars' m)
           -- FIXME these look backwards. Verify.
           , cSubCforS = rename (mkSubst (zip (mStateVars m) (mStateVars' m)))
           , cSubSforC = rename (mkSubst (zip (mStateVars' m) (mStateVars m)))
           , cKSem = sem
           }

-- | FIXME
mkAutomaton :: Model BDD -> Context BDD
            -> (AgentID, (KF, (BDD, BDD))) -> IO SPRAutomaton
mkAutomaton m ctxt autoInfo@(_aid, (_kf0, (outBit0, _outBit'))) =
  do auto <- Auto.mk m autoInfo
     let
         -- Construct the initial relation: a state is initially
         -- possible iff it is currently (initially) possible.
         -- @tv@ (later) represents the initial states.
         -- Set the Kauto outBits for the initial states.
         setKBit ss (_aid, (kf, (outBit, _outBit'))) =
           ss /\ (outBit <-> evalKSet m ctxt ss kf)

         init_rel = foldl' setKBit (mInitStates m) (mKconds m)

         -- Process each initial common observation.
         fcobs (ssco, _co) = mapObsM ssco (Auto.bmObs auto) (fobs ssco)

         -- Process the agent's initial observation.
         fobs ssco (sso, obs) = assert (ssco /\ sso == sso) $
           do let kfHolds = sso /\ outBit0 == sso
                  s = SPRState (ssco, sso)
              -- putStrLn $ "BroadcastSPR_init: " ++ show (renderFn (Auto.bmRenderObs auto) sso) ++ " / " ++ show kfHolds -- ++ " / " ++ show sso
              _ <- Auto.addInitialTransition auto obs s kfHolds
              mkAutomatonStep m ctxt auto s

         Just (cobs, _renderCObs) = mCommonObs m

     putStrLn $ "Constructing automaton for: " ++ show autoInfo
     putStrLn $ " observation width: " ++ show (length (Auto.bmObs auto))
     putStrLn "Building init_rel"
     init_rel `seq` putStrLn " ... finished init_rel"
     mapObsM init_rel cobs fcobs
     putStrLn " ... finished automaton"
     return auto

-- | Take a temporal step: FIXME
mkAutomatonStep :: Model BDD -> Context BDD -> SPRAutomaton -> SPRState -> IO ()
mkAutomatonStep m ctxt auto s@(SPRState (ssco0, sso0)) = assert (ssco0 /\ sso0 == sso0) $
  do let
         -- FIXME set the kbits in these sets.
         -- Set the Kauto outBits for the next states.
         setKBit ss (_aid, (kf, (outBit, _outBit'))) =
           ss /\ (outBit <-> evalKSet m ctxt ss kf)

         -- The sets of successors possible for the agent, and for the
         -- commonly-known set of states.
         ssco_next_kbits =
           foldl' setKBit (cSubCforS ctxt (rel_product (cGroupC ctxt) ssco0 (mTr m))) (mKconds m)
         sso_next_kbits =
           ssco_next_kbits /\ cSubCforS ctxt (rel_product (cGroupC ctxt) sso0 (mTr m))

         -- Process the common observation.
         fcobs (ssco, co) = mapObsM ssco (Auto.bmObs auto) (fobs co)

         -- Process each of the agent's observations.
         -- The common observation allows us to refine the common set of states.
         fobs co (sso, obs) =
           do let kfHolds = sso /\ Auto.bmOutBit auto == sso
                  t = SPRState (ssco_next_kbits /\ co, sso)
              -- putStrLn $ "BroadcastSPR_mkAutomatonStep: obs: " ++ show (renderFn (Auto.bmRenderObs auto) sso) ++ " / " ++ show kfHolds -- ++ " / " ++ show s ++ " / " ++ show t
              new <- Auto.addTransition auto s obs t kfHolds
              when new $ mkAutomatonStep m ctxt auto t

     -- Split on the successors of the agent's set of possible states.
     mapObsM sso_next_kbits (Auto.bmObs auto) fcobs

-- | Determine where the knowledge formula holds on the given relation
-- between initial and current/final states reachable at time /n/, all
-- with the same common observation.
evalKSet :: Model BDD -> Context BDD -> BDD -> KF -> BDD
evalKSet m ctxt nreachableStates = -- trace ("evalKSet") $
                                   propSat m (cKSem ctxt nreachableStates)
