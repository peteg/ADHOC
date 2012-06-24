{-# LANGUAGE NoMonomorphismRestriction #-}
{- Synthesis for single-agent synchronous perfect recall.
 - Copyright   :  (C)opyright 2006, 2009-2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -
 - Synthesis for:
 -   - synchronous perfect recall
 -   - single agent
 -   - atemporal
 -   --> KBPs with formulas of the form:
 -          K_a p(K_a q_1, ... K_a q_n, b_1, ..., b_n)
 -       where p describes some boolean combination of the arguments.
 -   - Explicit-state construction of a Moore-style automaton
 -}
module ADHOC.Knowledge.SingleSPR
    ( singleSPRSynth
    ) where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude hiding ( id, (.) )

import Control.Monad	( when )
import System.IO.Unsafe	( unsafePerformIO )

import Data.List	( union )

import ADHOC.Basis
import ADHOC.Constructivity ( isConstructive' )
import ADHOC.Model	( KF(..), KSem(..), propSat, Model(..), RenderFn, renderFn )

import ADHOC.Knowledge.ExplicitStateAutomata ( Hashable(..), Automaton, Minimize, Synth )
import qualified ADHOC.Knowledge.ExplicitStateAutomata as Auto

-------------------------------------------------------------------

-- | For single-agent perfect-recall, each automaton state is labelled
-- with the set of environment states that the agent considers
-- possible.
newtype SPRState b = SPRState b
                   deriving (Eq, Hashable, Ord, Show)

type SPRAutomaton b = Automaton b b (SPRState b)

singleSPRSynth :: Synth BDD (SPRState BDD) c
singleSPRSynth minType = fmap synth . isConstructive' 0
  where
    synth (m, c) = case mKconds m of
      [] -> (error "SyncPR: No automaton.", m, c)
      [autoInfo@(aid, (kf, _outBits))] ->
        case prGetAgentID kf of
          Just aid' | aid == aid' -> sprSynth m c autoInfo minType
          _ -> error $ "SyncPR.spr: KF not subjective or mentions multiple agents: " ++ show kf
      xs -> error $ "SyncPR.spr: expecting a single synthesis task, got " ++ show (length xs) ++ "."

-- | Ensure the knowledge formula only mentions a single agent.
prGetAgentID :: KF -> Maybe AgentID
prGetAgentID f0 =
    case gaid f0 of
      []    -> Nothing
      [aid] -> Just aid
      x     -> error $ "prGetAgentID: knowledge operators must be homogeneous (single-agent): " ++ show x
    where gaid :: KF -> [AgentID]
          gaid f =
              case f of
                KFfalse             -> []
                KFtrue              -> []
                KFprobe {}          -> []

                f1 `KFand` f2       -> gaid f1 `union` gaid f2
                f1 `KFor`  f2       -> gaid f1 `union` gaid f2
                f1 `KFxor` f2       -> gaid f1 `union` gaid f2
                f1 `KFimplies` f2   -> gaid f1 `union` gaid f2
                f1 `KFiff` f2       -> gaid f1 `union` gaid f2
                KFneg f1            -> gaid f1

                KFknows aid f1      -> [aid] `union` gaid f1
                KFknowsHat aid _l   -> [aid]
                KFcommon aids f1    -> aids `union` gaid f1
                KFcommonHat aids _l -> aids

----------------------------------------

-- | Synthesis for knowledge formulas.
sprSynth :: (BDDOps b, Hashable b, Ord b, Show b)
          => Model b -> c -> (AgentID, (KF, (b, b))) -> Minimize
          -> ([SPRAutomaton b], Model b, c)
sprSynth m c autoInfo minType = unsafePerformIO $
  do automaton <- Auto.minimize minType =<< mkAutomaton m autoInfo
     m' <- Auto.automata2model m [automaton]
     return ([automaton], m', c)

----------------------------------------

-- | Context for the DFA construction.
data Context b =
    Context
    { cGroupC :: Group b
    , cGroupS :: Group b
    , cSubCforS :: b -> b
    , cSubSforC :: b -> b
    , cAuto :: SPRAutomaton b
    }

-- | Construct the DFA using a DFS.
mkAutomaton :: forall b. (BDDOps b, Hashable b, Ord b, Show b)
            => Model b -> (AgentID, (KF, (b, b))) -> IO (SPRAutomaton b)
mkAutomaton m autoInfo@(aid, (kf, (outBit, _outBit'))) =
  do putStrLn $ "SingleSPR.mkAutomaton init agent: " ++ aid ++ " / " ++ show kf
     auto <- Auto.mk m autoInfo

     let ctxt = Context
           { cGroupC = mkGroup (mStateVars m)
           , cGroupS = mkGroup (mStateVars' m)
           , cSubCforS = rename (mkSubst (zip (mStateVars m) (mStateVars' m)))
           , cSubSforC = rename (mkSubst (zip (mStateVars' m) (mStateVars m)))
           , cAuto = auto
           }

         f (sso, obs) =
           do let kfHolds = (if evalKSet ctxt m sso (Auto.bmKF (cAuto ctxt)) /\ sso == sso then true else false) :: b
                  sso_kbit = sso /\ (outBit <-> kfHolds)
                  s = SPRState sso_kbit
              putStrLn $ "SingleSPR.mkAutomaton init: obs: " ++ show (renderFn (Auto.bmRenderObs auto) sso) ++ " / " ++ show (kfHolds :: b) -- ++ " / " ++ show s
              _ <- Auto.addInitialTransition auto obs s ((kfHolds :: b) == true)
              mkAutomatonStep m ctxt sso_kbit

     mapObsM (mInitStates m) (Auto.bmObs auto) f
     return auto

-- | Take a temporal step: for an element of the partition of the
-- temporal slice (wrt the agent's observation) @sso@, symbolically
-- compute the set of successors of those states and partition those.
mkAutomatonStep :: (Ord b, QBF b, Show b)
                => Model b -> Context b -> b -> IO ()
mkAutomatonStep m ctxt sso =
    mapObsM sso_next (Auto.bmObs (cAuto ctxt)) (partitionStates m ctxt sso)
  where
    sso_next = cSubCforS ctxt (rel_product (cGroupC ctxt) sso (mTr m))

-- | Process a successor state @t_sso@ of @s_sso@, and recursively
-- process its successors.
-- FIXME hoist the evalKSet up to mkAutomatonStep: set the kbit then partition.
partitionStates :: forall b. (Ord b, QBF b, Show b)
                => Model b -> Context b -> b -> (b, b) -> IO ()
partitionStates m ctxt s_sso (t_sso, obs) =
  do let kfHolds = (if evalKSet ctxt m t_sso (Auto.bmKF (cAuto ctxt)) /\ t_sso == t_sso then true else false) :: b
         outBit = Auto.bmOutBit (cAuto ctxt)
         t_sso_kbit = t_sso /\ (outBit <-> kfHolds)
         s = SPRState s_sso
         t = SPRState t_sso_kbit
     putStrLn $ "SingleSPR.partitionStates: obs: " ++ show (renderFn (Auto.bmRenderObs (cAuto ctxt)) t_sso) ++ " / " ++ show (kfHolds :: b) -- ++ " / " ++ show s ++ " / " ++ show t_sso
     new <- Auto.addTransition (cAuto ctxt) s obs t (kfHolds == true)
     when new $ mkAutomatonStep m ctxt t_sso_kbit

-- Exploit single-agent-ness here: K_a (K_a f) <-> K_a f.
evalKSet :: (QBF b, Eq b) => Context b -> Model b -> b -> KF -> b
evalKSet ctxt m ss = propSat m sem
  where
    groupS = cGroupS ctxt
    subSforC = cSubSforC ctxt

    sem = KSem
      { ksem = \_aid fsat -> if ss /\ fsat == ss then ss else false
      -- FIXME also could ensure a unique valuation for bs by folding
      , khatsem = \_aid bs -> if ss /\ forall groupS (subSforC ss --> valEq bs) == ss then ss else false
        -- Common knowledge is boring with a single agent
      , cksem = \_aids -> ksem sem []
      , ckhatsem = \_aids -> khatsem sem []
      }

    valEq bs = conjoin [ b <-> subSforC b | b <- bs ]
