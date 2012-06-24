{- Synthesis for multi-agent clock.
 - Copyright   :  (C)opyright 2009-2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -
 - Synthesis for:
 -   - clock semantics of knowledge
 -   - multi-agent
 -   - atemporal
 -   - Explicit-state construction of a Moore-style automaton
 -}
module ADHOC.Knowledge.Clock
    ( clockSynth
    ) where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude hiding ( id, (.) )

import Control.Monad	( foldM )
import System.IO.Unsafe	( unsafePerformIO )

import Data.List	( foldl' )

import Data.Set		( Set )
import qualified Data.Set as Set

import ADHOC.Basis
import ADHOC.Constructivity ( isConstructive' )
import ADHOC.Model	( KF(..), KSem(..), propSat, Model(..), RenderFn, renderFn )

import ADHOC.Knowledge.ExplicitStateAutomata ( Hashable(..), Automaton, Synth )
import qualified ADHOC.Knowledge.ExplicitStateAutomata as Auto

-------------------------------------------------------------------

-- | States of the constructed automata.
--
-- Consists of @(states reachable in /n/ steps, equivalence class (set
-- of states) that the agent considers possible)@.
newtype ClockState b = ClockState (b, b)
                       deriving (Eq, Ord)

instance Hashable b => Hashable (ClockState b) where
  hash (ClockState (x, y)) = hash (x, y)

type ClockAutomaton b = Automaton b b (ClockState b)

-------------------------------------------------------------------

-- FIXME Haskell doesn't support top-level monadic bindings, so hack
-- around that here. This is pretty safe modulo the debugging output.
clockSynth :: Synth BDD (ClockState BDD) c
clockSynth minType = fmap synth . isConstructive' 0
  where
    synth (m, c) = unsafePerformIO $
      do automata0 <- mkAutomata m
         -- Auto.dump "/tmp/before" automata0
         automata <- mapM (Auto.minimize minType) automata0
         m' <- Auto.automata2model m automata
         return (automata, m', c)

----------------------------------------

-- The automata construction is essentially a BFS-style search. We
-- proceed in "levels", i.e. temporal slices.

-- The state of the automaton construction process.
--   - Invariant: once a state has been visited (is in 'baAutomaton')
--     it never appears in 'baFrontier' again.
--
-- FIXME all "constant" apart from baFrontier (due to mutability in
-- baAutomaton), so we make it an IORef ??
data BAState b =
    BAState
    { baFrontier :: Set (ClockState b)
    , baAutomaton :: ClockAutomaton b
    }

-- | FIXME
data ConstructionState b =
    ConstructionState
    { csSS :: b -- ^ FIXME
    , csASs :: [BAState b] -- ^ FIXME
    }

-- | Miscellaneous context for the automata construction process.
data Context b =
    Context
    { cGroupC :: Group b
    , cGroupS :: Group b
    , cSubCforS :: b -> b
    , cSubSforC :: b -> b
    }

----------------------------------------

-- | Does the fixpoint and iteration over the frontier.
mkAutomata :: (BDDOps b, Hashable b, Ord b, Show b)
            => Model b
            -> IO [ClockAutomaton b]
mkAutomata m =
  do let ctxt = Context
           { cGroupC = mkGroup (mStateVars m)
           , cGroupS = mkGroup (mStateVars' m)
           , cSubCforS = rename (mkSubst (zip (mStateVars m) (mStateVars' m)))
           , cSubSforC = rename (mkSubst (zip (mStateVars' m) (mStateVars m)))
           }
     initASs <- mkAutomataInit m ctxt
     finalASs <- untilM (return . all (Set.null . baFrontier) . csASs)
                        (mkAutomataStep m ctxt)
                        initASs
     return [ baAutomaton bas | bas <- csASs finalASs ]

----------------------------------------

-- | Initial state in the automata construction process.
mkAutomataInit :: (Hashable b, QBF b, Ord b, Show b)
               => Model b -> Context b -> IO (ConstructionState b)
mkAutomataInit m ctxt =
  do let
         -- Set the Kauto outBits for the initial states.
         setKBit ss (_aid, (kf, (outBit, _outBit'))) =
           ss /\ (outBit <-> evalKSet m ctxt ss kf)

         ss_kbits = foldl' setKBit (mInitStates m) (mKconds m)

         -- Add the initial transitions to the automaton.
         mkAutomatonInit autoInfo@(aid, (kf, (outBit, _outBit'))) =
           do -- putStrLn $ "Clock.mkAutomatonInit: agent: " ++ aid ++ " / " ++ show kf
              auto <- Auto.mk m autoInfo
              let f astates (sso, obs) =
                    do let kfHolds = sso /\ outBit == sso
                           s = ClockState (ss_kbits, sso)
                       -- putStrLn $ "Clock.mkAutomatonInit: obs: " ++ show (renderFn (Auto.bmRenderObs auto) obs) ++ " / " ++ show kfHolds
                       _ <- Auto.addInitialTransition auto obs s kfHolds
                       return $ Set.insert s astates
              initialStates <- foldObsM ss_kbits (Auto.bmObs auto) f Set.empty
              return BAState { baFrontier = initialStates
                             , baAutomaton = auto }

     ass <- mapM mkAutomatonInit (mKconds m)
     return ConstructionState { csSS = ss_kbits, csASs = ass }

----------------------------------------

-- | Update each automaton in sequence.
mkAutomataStep :: (Ord b, QBF b, Show b)
               => Model b -> Context b -> ConstructionState b -> IO (ConstructionState b)
mkAutomataStep m ctxt cstate =
  do let
         -- Set the Kauto outBits for the next states.
         setKBit ss (_aid, (kf, (outBit, _outBit'))) =
           ss /\ (outBit <-> evalKSet m ctxt ss kf)

         ss_next_kbits = foldl' setKBit
                                (cSubCforS ctxt (rel_product (cGroupC ctxt) (csSS cstate) (mTr m)))
                                (mKconds m)

         mkAutomatonStep bas0 =
           foldObsM ss_next_kbits
                    aObs
                    (partitionStates aRenderObs ss_next_kbits (Set.toList (baFrontier bas0)))
                    (bas0{baFrontier = Set.empty})
           where
             Just (aObs, aRenderObs) = lookup (Auto.bmAgentID (baAutomaton bas0)) (mAgents m)

     as' <- mapM mkAutomatonStep (csASs cstate)
     return ConstructionState { csSS = ss_next_kbits, csASs = as' }

-- | This function is folded across the partition of @ss@ by @foldObs@.
--
-- This is where we do the "level" thing, plugging in too many transitions.
partitionStates :: forall b. (Boolean b, Ord b)
                => RenderFn b -> b -> [ClockState b]
                -> BAState b -> (b, b) -> IO (BAState b)
partitionStates renderObs ss_next_kbits prev_frontier bas (t_sso_kbits, obs) =
  do let kfHolds = t_sso_kbits /\ Auto.bmOutBit (baAutomaton bas) == t_sso_kbits
         t = ClockState (ss_next_kbits, t_sso_kbits)
         f tb s = fmap (|| tb) $ Auto.addTransition (baAutomaton bas) s obs t kfHolds
     -- putStrLn $ "Clock.partitionStates obs: " ++ show (renderFn renderObs t_sso_kbits) ++ " / " ++ show kfHolds
     tb <- foldM f False prev_frontier
     return $ if tb then bas{ baFrontier = t `Set.insert` baFrontier bas } else bas

-- | Determine where the knowledge formula holds on the given set of
-- states reachable in time /n/.
evalKSet :: (QBF b, Show b) => Model b -> Context b -> b -> KF -> b
evalKSet m ctxt nreachableStates = propSat m sem
  where
    groupS = cGroupS ctxt
    subSforC = cSubSforC ctxt
    nreachableStates' = subSforC nreachableStates

    -- FIXME could stage this better for when KF contains many knowledge subformulas.
    sem = KSem
      { ksem = \aid fsat -> forall groupS ((nreachableStates' /\ obsEq aid)
                                           --> subSforC fsat)
      , khatsem = \aid bs -> forall groupS ((nreachableStates' /\ obsEq aid)
                                           --> valEq bs)
      }

    valEq bs = conjoin [ b <-> subSforC b | b <- bs ]

    -- FIXME this is the same at each time step? May as well float it.
    obsEq aid = valEq aObs
      where Just (aObs, _aRenderObs) = lookup aid (mAgents m)
