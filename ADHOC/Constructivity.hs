{-# OPTIONS_GHC -fno-ignore-asserts #-}
{-# LANGUAGE TypeFamilies, UndecidableInstances #-}
{- Constructivity analysis for cyclic circuits.
 - Copyright   :  (C)opyright 2004-2006, 2009-2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -}
module ADHOC.Constructivity
    ( CArrow
    , isConstructive'
    , isConstructive
    , unstableTrace
    ) where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude hiding ( id, (.) )
import Control.Monad    ( liftM2, when )
import Text.PrettyPrint as PP

import Control.Arrow.Operations        ( ArrowState(..) )
import Control.Arrow.Transformer.State ( StateArrow, runState )
import ADHOC.Circuits
import ADHOC.Patterns ( zipWith3A )
import ADHOC.Generics
import ADHOC.Model ( ArrowAgent(..), ArrowBroadcast(..), ArrowKTest(..),
                     CBool(..), chooseState',
                     KF, ensureSubjective,
                     Model(..), ArrowProbe(..),
                     RenderInState(..), RenderFn(..), nullRenderFn, combineRenderFns )
import ADHOC.NonDet
import ADHOC.Data.SizedLists

import Data.List ( genericReplicate )

import Data.Map ( Map )
import qualified Data.Map as Map

import Data.Sequence hiding ( length, null, zip, zipWith )
import qualified Data.Sequence as Seq
import Data.Foldable ( toList )

-------------------------------------------------------------------

-- | Command combinator: update the store.
--
-- Often @fA@ is pure, but we typically want to pass it values that
-- are 'Arrow' bound, and so using this combinator is syntactially
-- heavy.
updateStateAC :: Arrow (~>) => ((env, s) ~> (v, s)) -> StateArrow s (~>) env v
updateStateAC fA = id &&& fetch >>> lift fA >>> second store >>> arr fst
{-# INLINE updateStateAC #-}

-------------------------------------------------------------------
-- A dual-rail encoding of the (flat) 'Boolean' domain.
--
-- Shiple/Berry/Touati's representation is (f0, f1) where "f1 (resp f0)
-- is the characteristic function of the set of inputs for which f
-- evaluates to 1 (resp 0)."
--
-- Concretely:
--      Bot  (0, 0)
--      0    (1, 0)
--      1    (0, 1)
--
-- Note that the functions we provide may not behave properly on the
-- other value (1, 1) - we make no use of "Top" here.
-------------------------------------------------------------------

-- | 'CArrow' simulates the circuit over two rails.
newtype TwoRails b = TR { unTR :: (b, b) }
    deriving (Eq, Show)

instance Functor TwoRails where
    fmap f (TR (x, y)) = TR (f x, f y)

instance Applicative TwoRails where
    pure a = TR (a, a)
    TR (f, g) <*> TR (x, y) = TR (f x, g y)

trBottom :: TwoRails CBool
trBottom = TR (CBool false, CBool false)

trEq :: TwoRails CBool -> TwoRails CBool -> Bool
trEq (TR (CBool xf, CBool xt)) (TR (CBool yf, CBool yt)) = xf == yf && xt == yt

trIsBottom :: TwoRails CBool -> BDD
trIsBottom (TR (CBool xf, CBool xt)) = neg (xf \/ xt)

trConst :: Arrow (~>) => (BDD, BDD) -> env ~> TwoRails CBool
trConst (cf, ct) = arr (const (TR (CBool cf, CBool ct)))

-------------------------------------------------------------------
-- Synchronous circuit constructivity arrows.
--
-- Verifies that a given circuit is constructive and builds an
-- equivalent standard model by running the arrow over the 'TwoRail'
-- domain.
-------------------------------------------------------------------

-- | Static information.
data Static =
    Static
    { sNumLoops :: !Int -- ^ Number of combinational loops
    , sCounter :: !Integer -- ^ Uniquifier
    , sBoot :: (BDD, BDD) -- ^ Are we in the initial/boot state?
    , sRenderFn :: RenderFn BDD -- ^ A function for rendering (part of) a system state.
    , sStateVars  :: [BDD] -- ^ Current-state BDD variables
    , sStateVars' :: [BDD] -- ^ Next-state BDD variables
    , sNumTmpVars :: Integer -- ^ The number of temporary variables
    , sTmpVars  :: [[BDD]] -- ^ \"Temporary\" state variables
    , sSchedFairVars  :: [BDD] -- ^ Current-state fair scheduling variables
    , sAgents :: Map AgentID ([BDD], RenderFn BDD) -- ^ Map agents to their observations of their local state, and a function for rendering these observations
    , sCurrentAgentID :: AgentID -- ^ The current agent context (if any)
    , sKTests :: [(AgentID, (KF, (BDD, BDD)))] -- ^ Each agent can evaluate zero or more knowledge formulas, with results communicated via the given variable (current/next state pair).
    , sCurrentObs :: [BDD] -- ^ The state variables in the scope of a current \"agent\" construct
    }

-- | Initial static information.
--
-- The argument is how many temporary variables we need to allocate.
static0 :: Integer -> Static
static0 numTmpVars =
    Static
    { sNumLoops = 0
    , sCounter = 0
    , sBoot = (bootv, bootv')
    , sRenderFn = nullRenderFn
    , sStateVars   = [bootv]
    , sStateVars'  = [bootv']
    , sNumTmpVars = numTmpVars
    , sTmpVars = boot_tmpVars
    , sSchedFairVars  = []
    , sAgents = Map.empty
    , sCurrentAgentID = error "no current agent"
    , sKTests = []
    , sCurrentObs = []
    }
  where
    (bootv, bootv', boot_tmpVars) = allocVars "@boot" numTmpVars

allocVars :: String -> Integer -> (BDD, BDD, [[BDD]])
allocVars vid numTmpVars = (v, v', tmpVars')
  where
    v : v' : tmpVars = bvars $ [ vid, prime vid ] ++ map (\i -> vid ++ "_" ++ show i) [ 1 .. numTmpVars ]
    tmpVars' = map (:[]) tmpVars

-- | Dynamic information passed along the "wires".
--
-- @tmpVars@ tracks how many additional temporary variables to
-- allocate.
data Dynamic =
    Dynamic
    { dFixChanged :: Bool -- ^ Have any of the fixpoints changed on this iteration?
    , dFixState :: Seq (TwoRails CBool) -- ^ State of the fixpoint computations
    , dInit :: BDD -- ^ Initial states
    , dTr :: BDD -- ^ Transition relation
    , dAgents :: Map AgentID ([BDD], RenderFn BDD) -- ^ Map agents to their observations of the environment, and a function for rendering it
    , dCommonObs :: Maybe ([BDD], RenderFn BDD) -- ^ The agents' common observation, and a function for rendering it
    , dProbes :: Map ProbeID ([BDD], RenderFn BDD)
    } deriving Show

-- | Initial dynamic information.
dynamic0 :: Static -> Dynamic
dynamic0 s =
    Dynamic
    { dFixChanged = False
    , dFixState = Seq.fromList [ trBottom | _ <- [1 .. sNumLoops s] ]
    , dInit = fst (sBoot s) -- Boot bit is initially true
    , dTr = neg (snd (sBoot s)) -- Boot bit is always false in the next step.
    , dAgents = Map.empty
    , dCommonObs = Nothing
    , dProbes = Map.empty
    }

-- | Generate a standard model from the "TwoRails" simulation.
--
-- We don't quantify out the scheduling variables for (unfair)
-- non-determinism from the vector of state variables as probes,
-- agents, etc. may be observing them.
mkModel :: Static -> Dynamic -> Model BDD
mkModel s dyn =
    Model
    { mStateVars   = sStateVars  s
    , mStateVars'  = sStateVars' s
    , mTmpVars     = sTmpVars s
    , mInitStates  = dInit dyn
    , mTr          = dTr dyn
    , mSchedFairVars = sSchedFairVars s
    , mAgents      = Map.toList (Map.unionWith agentCombine (sAgents s) (dAgents dyn))
    , mCommonObs   = dCommonObs dyn
    , mKconds      = sKTests s
    , mProbes      = dProbes dyn
    }
  where
    agentCombine (sObs, sRender) (dObs, dRender) =
        ( sObs ++ dObs
        , case (null sObs, null dObs) of
            (False, False) -> combineRenderFns "St: " sRender "Obs: " dRender
            (True,  False) -> dRender
            (False, True)  -> sRender
            (True,  True)  -> RenderFn (const PP.empty)
        )

----------------------------------------

-- | Map dynamic state and some inputs to a new dynamic state and some
-- outputs.
newtype DynArr b c =
  DynArr { runDynArr :: StateArrow Dynamic (->) (TwoRails b) (TwoRails c) }

-- | Lift a pure 'TwoRails' function to a stateful 'TwoRails' 'DynArr'.
dynLift :: (TwoRails b -> TwoRails c) -> DynArr b c
dynLift = DynArr . arr
{-# INLINE dynLift #-}

instance Category DynArr where
  id = DynArr id
  DynArr f . DynArr g = DynArr $ f . g

instance Arrow DynArr where
  arr f = DynArr $ lift $ arr unTR >>> f *** f >>> arr TR
  first f = DynArr $ proc (TR ((b0, d0), (b1, d1))) ->
    do TR (c0, c1) <- runDynArr f -< TR (b0, b1)
       returnA -< TR ((c0, d0), (c1, d1))
  second f = DynArr $ proc (TR ((b0, d0), (b1, d1))) ->
    do TR (c0, c1) <- runDynArr f -< TR (d0, d1)
       returnA -< TR ((b0, c0), (b1, c1))
  f *** g = DynArr $ proc (TR ((b0, d0), (b1, d1))) ->
    do TR (c0, c1) <- runDynArr f -< TR (b0, b1)
       TR (e0, e1) <- runDynArr g -< TR (d0, d1)
       returnA -< TR ((c0, e0), (c1, e1))

instance ArrowLoop DynArr where
  loop fA = DynArr $ proc (TR (bf, bt)) ->
    do rec TR ((cf, df), (ct, dt)) <- runDynArr fA -< TR ((bf, df), (bt, dt))
       returnA -< TR (cf, ct)

instance ArrowComb DynArr where
  -- The type of a single rail.
  type B DynArr = CBool

  falseA = DynArr $ trConst (true, false)
  trueA  = DynArr $ trConst (false, true)

  andA = DynArr $ arr $ \(TR ((CBool xf, CBool yf), (CBool xt, CBool yt))) ->
    TR (CBool (xf \/ yf), CBool (xt /\ yt))

  notA = DynArr $ arr $ \(TR (xf, xt)) -> TR (xt, xf)

  orA = DynArr $ arr $ \(TR ((CBool xf, CBool yf), (CBool xt, CBool yt))) ->
    TR (CBool (xf /\ yf), CBool (xt \/ yt) )

  xorA = DynArr $ arr $ \(TR ((CBool xf, CBool yf), (CBool xt, CBool yt))) ->
    TR (CBool (xf <-> yf), CBool (xt `xor` yt) )

  iffA = DynArr $ arr $ \(TR ((CBool xf, CBool yf), (CBool xt, CBool yt))) ->
    TR (CBool (xf `xor` yf), CBool (xt <-> yt) )

----------------------------------------

-- | The constructivity 'Arrow': accumulates static information about
-- the circuit and creates a dynamic arrow that builds the set of
-- initial states and the transition relation (etc).
newtype CArrow b c =
    CArrow { runCArrow :: StateM Static (DynArr b c) }

-- | Lift a purely-dynamic 'DynArr'.
dynArr :: DynArr b c -> CArrow b c
dynArr = CArrow . return

instance Category CArrow where
  id = CArrow $ return id
  f . g = CArrow $ liftM2 (.) (runCArrow f) (runCArrow g)

instance Arrow CArrow where
  arr = CArrow . return . arr
  first = CArrow . fmap first . runCArrow
  second = CArrow . fmap second . runCArrow
  f *** g = CArrow $ liftM2 (***) (runCArrow f) (runCArrow g)

instance ArrowLoop CArrow where
  loop f = CArrow $ runCArrow f >>= return . loop

instance ArrowComb CArrow where
  -- The type of a single rail.
  type B CArrow = CBool

  falseA = dynArr falseA
  trueA  = dynArr trueA

  andA = dynArr andA
  notA = dynArr notA
  nandA = dynArr nandA
  orA  = dynArr orA
  xorA = dynArr xorA
  iffA = dynArr iffA
  impA = dynArr impA

instance Zero CArrow CBool where
  zeroA = falseA

----------------------------------------

instance Structure CBool v => ArrowMux CArrow v where
  muxA = proc (sel, (va, vb)) ->
    do out <- zipWith3A width muxA_bit -< ( genericReplicate width sel
                                          , destructure va
                                          , destructure vb)
       returnA -< fst (runStateM structure out)
    where
      width = c2num (undefined :: SIwidth CBool v) :: Integer

      muxA_bit = proc (sel, a, b) ->
        do sela <- andA -< (sel, a)
           selb <- andA <<< first notA -< (sel, b)
           orA -< (sela, selb)

instance ArrowInit CArrow where
  isInitialState = CArrow $
    do s <- getSM
       let (bv, _bv') = sBoot s
       return $ dynLift (trConst (neg bv, bv))

-- | Record the probe projections in the dynamic state.
--
-- If a label is multiply defined then it can only be used when
-- printing out the state (and not as a proposition).
instance (StructureDest CBool v, RenderInState v BDD)
      => ArrowProbe CArrow v where
  probeA l = dynArr $ DynArr $ proc v@(TR(_vf, vt)) ->
      (| updateStateAC (\dyn -> returnA -< (v, dyn{ dProbes = Map.insertWith lunique l (dest' vt, renderInState vt) (dProbes dyn) })) |)
    where
      dest' = map cbool2bdd . destructure
      lunique (_, risN) (_, risO) = ( error $ "probeA: \"" ++ l ++ "\" is multiply defined, and cannot be used as a proposition."
                                    , risO `mappend` risN)

----------------------------------------

-- | We ensure that every loop in the circuit is well-defined, even if
-- it does not affect the visible output. Berry et al call this
-- /strong constructivity/. This property depends on not having a
-- 'bottomA' constant, i.e. the only possible sources of undefinedness
-- are combinational loops.
--
-- FIXME this could actually treat all loops that can be decomposed to
-- bits, ala ArrowMux / ArrowDelay.

instance ArrowCombLoop CArrow CBool where
  combLoop f = CArrow $
    do fA <- runCArrow f
       n <- modifySM (\s -> (sNumLoops s, s{sNumLoops = succ (sNumLoops s)}))

       let dcloop = proc b@(TR (bf, bt)) ->
             do dyn <- fetch -< ()
                let d@(TR (df, dt)) = dFixState dyn `Seq.index` n
                TR ((cf, df'), (ct, dt')) <- runDynArr fA -< TR ((bf, df), (bt, dt))
                let d' = TR (df', dt')
                if d `trEq` d'
                  then returnA -< TR (cf, ct)
                  else do (| updateStateAC (\dyn' ->
                               returnA -< ((), dyn{ dFixChanged = True
                                                  , dFixState = Seq.update n d' (dFixState dyn') })) |)
                          dcloop -< b
       return $ DynArr dcloop

----------------------------------------

-- This requires {-# LANGUAGE UndecidableInstances #-}
instance (Structure CBool v, RenderInState v BDD)
      => ArrowDelay CArrow v where
  delayA = muxA <<< isInitialState &&& delayArr
    where
      width = c2num (undefined :: SIwidth CBool v) :: Integer

      delayArr = CArrow $
        do -- Allocate the variables.
           (sbdds, sbdds') <- newStateVars "@st_" True width
           let svs = map CBool sbdds
               neg_svs = map (CBool . neg) sbdds

               inst_svs = fst (runStateM structure svs)
               inst_neg_svs = fst (runStateM structure neg_svs)

           -- Capture the rendering of this part of the state.
           -- FIXME how do we know what part of the state is what? Use a note/context/... ?
           modifySM (\s -> ((), s{ sRenderFn = combineRenderFns "S:" (renderInState inst_svs) "" (sRenderFn s) }))

           let toBDD :: [BDD] -> v -> BDD
               toBDD vars v = conjoin [ var <-> val | (var, CBool val) <- zip vars (destructure v) ]

               -- Bind the results of the arrows to the BDD variables
               -- representing the delay.
               --
               -- Inductively we assume that the state is
               -- well-defined, so we can get away with a single rail
               -- later on. We pass on the initial values in the
               -- initial instant (see above) so that the
               -- constructivity checker works in the standard way.
               --
               -- FIXME We need to check that the initialiser isn't
               -- defined in terms of the state variables for this
               -- delay - otherwise the initial state is only
               -- partially constrained.
               darr = proc (TR ((uf, _vf), (ut, vt))) ->
                 do (| updateStateAC (\dyn -> returnA -< ((), dyn{ dInit = toBDD sbdds ut /\ dInit dyn
                                                                 , dTr = toBDD sbdds' vt /\ dTr dyn})) |)
                    returnA -< TR ((uf, inst_neg_svs), (ut, inst_svs))

           return $ DynArr darr

instance (Structure CBool v, RenderInState v BDD)
      => ArrowUnsafeNonDet CArrow v where
  -- FIXME this might be buggy, see 08_Kes/14x + nondetE in Kesterel
  unsafeNonDetInstAC predA = CArrow $
    do (sbdds, _sbdds') <- newStateVars "@st_" True width
       let svs = map CBool sbdds
           neg_svs = map (CBool . neg) sbdds

           inst_svs = fst (runStateM structure svs)
           inst_neg_svs = fst (runStateM structure neg_svs)

       modifySM (\s -> ((), s{ sRenderFn = combineRenderFns "S:" (renderInState inst_svs) "" (sRenderFn s) }))

       pA <- runCArrow predA

       let darr = proc (TR (ef, et)) ->
             do TR (_uf, ut) <- runDynArr pA -< TR ((ef, inst_neg_svs), (et, inst_svs))
                (| updateStateAC (\dyn -> returnA -< ((), dyn{ dInit = cbool2bdd ut /\ dInit dyn
                                                             , dTr = cbool2bdd ut /\ dTr dyn })) |)
                returnA -< TR (inst_neg_svs, inst_svs)

       return $ DynArr darr
    where
      width = c2num (undefined :: SIwidth CBool v) :: Integer

  unsafeNonDetAC predA newA = CArrow $
    do (sbdds, sbdds') <- newStateVars "@st_" True width
       let svs = map CBool sbdds
           neg_svs = map (CBool . neg) sbdds

           inst_svs = fst (runStateM structure svs)
           inst_neg_svs = fst (runStateM structure neg_svs)

       modifySM (\s -> ((), s{ sRenderFn = combineRenderFns "S:" (renderInState inst_svs) "" (sRenderFn s) }))

       iA <- runCArrow predA
       nA <- runCArrow newA

       let -- If new says no, use the given value. If it says yes,
           -- choose a new value satisfying the predicate.
           newOrOld (CBool p) (CBool new) =
                (new --> subSforC p)
             /\ (neg new --> conjoin (zipWith (<->) sbdds sbdds'))

           subSforC = rename (mkSubst (zip sbdds sbdds'))

           darr = proc (env@(TR (ef, et))) ->
             do TR (_uf, ut) <- runDynArr iA -< TR ((ef, inst_neg_svs), (et, inst_svs))
                (| updateStateAC (\dyn -> returnA -< ((), dyn{dInit = cbool2bdd ut /\ dInit dyn})) |)
                TR (_bf, bt) <- runDynArr nA -< env
                (| updateStateAC (\dyn -> returnA -< ((), dyn{dTr = newOrOld ut bt /\ dTr dyn})) |)
                returnA -< TR (inst_neg_svs, inst_svs)

       return $ DynArr darr
    where
      width = c2num (undefined :: SIwidth CBool v) :: Integer

----------------------------------------

-- | The state is always defined, and therefore only requires a
-- @(currentState, nextState)@ pair, not a pair of dual-rail
-- variables.
--
-- \"Temporary\" variables adjacent to this pair are provided for use
-- by the synthesis algorithms.
--
-- @kTest@ variables are not observable; these are a function of the
-- observation so adding them provides no new information, and
-- possibly leads to headaches in the synthesis algorithms.
newStateVars :: String -> Bool -> Integer -> StateM Static ([BDD], [BDD])
newStateVars prefix observable n =
  modifySM (\s ->
    let newVar i = allocVars (prefix ++ show i) (sNumTmpVars s)
        (svs, svs', tvs) = unzip3 (map newVar [sCounter s .. sCounter s + n - 1])
     in ( (svs, svs')
        , s{ sCounter     = sCounter s + n
           , sStateVars   = svs    ++ sStateVars   s
           , sStateVars'  = svs'   ++ sStateVars'  s
           , sTmpVars     = foldr (zipWith (++)) (sTmpVars s) tvs
           , sCurrentObs  = (if observable then svs else []) ++ sCurrentObs s
           } ) )

-- | Scheduling variables (really auxiliary inputs) are always
-- defined.
--
-- Non-determinism within an agent is observable by the agent.
--
-- Here We do not care about the scheduling variable for the successor
-- state: it is chosen in complete ignorance of the current one.
newSchedVarPair :: Bool -> CArrow () CBool
newSchedVarPair isFair = CArrow $
  do ([sv], [_sv']) <- newStateVars "@sched" True 1
     when isFair $ modifySM (\s -> ((), s{sSchedFairVars = sv : sSchedFairVars s}))
     return $ DynArr $ trConst (neg sv, sv)

-- | Non-determinism.
-- This requires {-# LANGUAGE UndecidableInstances #-}
instance ArrowMux CArrow v => ArrowNonDet CArrow v where
  nondetA = proc vs ->
    do b <- newSchedVarPair False -< ()
       muxA -< (b, vs)

  nondetFairA = proc vs ->
    do b <- newSchedVarPair True -< ()
       muxA -< (b, vs)
{-

FIXME

This doesn't handle nested nondetFairA as one would expect.

If we have a `nondetFairA` (b `nondetFairA` c) we will be fair with
respect to the two choices separately, whereas what we want is to be
fair to them together. Concretely we are fair wrt a, but not to the
choice between b and c. (We might choose c whenever a gets chosen, and
b whenever b `nondetFairA` c gets chosen.)

The solution is to have the fairness constraints:

sv1 == sched var for a `nondetFairA` XXX
sv2 == sched var for XXX = b `nondetFairA` c

sv1
not sv1 /\ sv2
not asv /\ not sv2c

i.e. n + 1 constraints for n nested choices.

-}

----------------------------------------

-- FIXME abstraction breakage? BDD should be CBool ??
instance (StructureDest CBool obs, RenderInState obs BDD)
      => ArrowAgent CArrow obs where
  agent aid f = CArrow $
    do s <- modifySM (\s -> (s, s{ sRenderFn = nullRenderFn, sCurrentObs = [], sCurrentAgentID = aid }))
       fA <- runCArrow f
       modifySM (\s' -> ((), s'{ sAgents = Map.insert aid (sCurrentObs s', sRenderFn s') (sAgents s')
                               , sRenderFn = combineRenderFns "E" (sRenderFn s) "A" (sRenderFn s')
                               , sCurrentObs = sCurrentObs s' ++ sCurrentObs s
                               , sCurrentAgentID = sCurrentAgentID s }))
       return $ DynArr captureObs >>> fA
    where
      dest' = map cbool2bdd . destructure

      captureObs = proc obs@(TR (_obsf, obst)) ->
        (| updateStateAC (\dyn -> returnA -< (obs, dyn{dAgents = Map.insert aid (dest' obst, renderInState obst) (dAgents dyn)})) |)

-- FIXME verify that all agents are under the broadcast
-- FIXME verify that there is only one broadcast

instance (Zero CArrow iobs,
          StructureDest CBool cobs, RenderInState cobs BDD,
          StructureDest CBool iobs, Structure CBool iobs, RenderInState iobs BDD)
      => ArrowBroadcast CArrow iobs cobs where
  broadcast agents ienvA cobsA = proc env ->
    do ienv <- ienvA -< env
       cobs <- captureCommonObs <<< cobsA -< env
       arrs -< (ienv, cobs)
    where
      dest' = map cbool2bdd . destructure

      f (aid, iA, aA) acc = proc e@(ienv, cobs) ->
            do iobs <- (| muxAC (isInitialState -< ()) (iA -< ienv) (zeroA -< ()) |)
               c <- agent aid aA -< (iobs, cobs)
               cs <- acc -< e
               returnA -< c : cs

      arrs = foldr f (arr (const [])) (unSizedListA agents) >>> sizedListA

      -- FIXME check that dCommonObs == Nothing
      captureCommonObs = dynArr $ DynArr $ proc cobs@(TR (_cobsf, cobst)) ->
        (| updateStateAC (\dyn -> returnA -< (cobs, dyn{dCommonObs = Just (dest' cobst, renderInState cobst)})) |)

-- | Add a bit to the state to represent the output of the knowledge
-- automaton.
instance ArrowKTest CArrow where
  kTest kf = CArrow $
    do ([sv], [sv']) <- newStateVars "@kauto" False 1
       aid <- modifySM (\s -> (sCurrentAgentID s, s{ sKTests = (sCurrentAgentID s, (kf, (sv, sv'))) : sKTests s }))
       aid `seq` ensureSubjective aid kf `seq` return $ DynArr $ trConst (neg sv, sv)

----------------------------------------
-- Shiple/Berry/Touati's algorithm.
-- 1. The above 'Arrow' instances yield the dual-rail semantics.
-- 2. Compute the set of inputs and states that lead to instability.
-- 3. Compute reachability of these states by forward iteration.
--
-- FIXME we could provide better diagnostics here:
--  - the unstableDomain for delay-free circuits
--  - a backtrace for sequential circuits.
----------------------------------------

-- | Constructivity analysis for a closed circuit.
isConstructive' :: forall c. Integer -> CArrow () c -> Maybe (Model BDD, c)
isConstructive' numTmpVars fA =
  -- trace ("InitStates: " ++ show (dInit dyn)) $
  -- trace ("unstableStates: " ++ show unstableStates) $
  -- trace ("dFixState: " ++ show (dFixState dyn)) $
  if sNumLoops s == 0
     || unstableStates == false
     || not reachesUnstableState
    then
      let m = mkModel s dyn
      in -- trace ("isConstructive': numTmpVars = " ++ show numTmpVars ++ " / length mTmpVars = " ++ show (length (mTmpVars m))) $
         assert (length (mStateVars m) == length (mStateVars' m)
              && length (mTmpVars m) == fromInteger numTmpVars
              && all (\x -> length x == length (mStateVars m)) (mTmpVars m)) $
           m `seq` Just (m, ct)
    else Nothing
  where
    inVal = TR ((), ())
    (dynf, s) = runStateM (runCArrow fA) (static0 numTmpVars)
    dyn0 = dynamic0 s
    (TR (_cf, ct), dyn) = runState (runDynArr dynf) (inVal, dyn0)

    -- Yields the set of single-rail (inputs, state
    -- variables) that lead to a bottom output.
    -- This is sufficient for circuits without delays.
    unstableStates :: BDD
    unstableStates = disjoin (fmap trIsBottom (toList (dFixState dyn)))

    -- Forward reachability of an unstable state, assuming no
    -- constraints on the inputs.
    groupC = mkGroup (sStateVars s)
    subCforS = mkSubst (zip (sStateVars' s) (sStateVars s))
    forwardR ss0 ss
                 -- | trace ("forwardR: " ++ show ss) False = undefined
                 | ss /\ unstableStates /= false = trace ("unstableStates is reachable!") $ True
                 | ss0 == ss = False
                 -- | trace ("step: " ++ show (rename subCforS (rel_product groupC ss (dTr dyn)))) False = undefined
                 | otherwise = forwardR ss (ss \/ (rename subCforS
                                                      (rel_product groupC ss (dTr dyn))))

    reachesUnstableState = forwardR false (dInit dyn)

-- | Poor-man's constructivity analysis for an open circuit.
--
-- Close the circuit by (unfairly) non-deterministically choosing all
-- inputs. In general the user would like to provide a care set.
--
-- FIXME we could do this with a predicate @v ~> B (~>)@.
isConstructive :: Structure CBool b => CArrow b c -> Maybe (Model BDD, c)
isConstructive f = isConstructive' 0 (f <<< nondetInstA)

--------------------

-- | Print a trace that leads to an unstable state. Assumes there is one.
unstableTrace :: CArrow () c -> IO ()
unstableTrace fA = mapM_ showState (forwardR (backwardR unstableStates []))
  where
    inVal = TR ((), ())
    (dynf, s) = runStateM (runCArrow fA) (static0 0)
    dyn0 = dynamic0 s
    (TR (_cf, _ct), dyn) = runState (runDynArr dynf) (inVal, dyn0)

    groupC = mkGroup (sStateVars s)
    groupS = mkGroup (sStateVars' s)
    subCforS = mkSubst (zip (sStateVars' s) (sStateVars s))
    subSforC = mkSubst (zip (sStateVars s) (sStateVars' s))

    unstableStates :: BDD
    unstableStates = disjoin (fmap trIsBottom (toList (dFixState dyn)))

    backwardR :: BDD -> [BDD] -> [BDD]
    backwardR ss p =
      let ssInit = dInit dyn /\ ss
       in if ssInit /= false
            then ssInit : p
            else backwardR (rel_product groupS (rename subSforC ss) (dTr dyn)) (ss : p)

    forwardR :: [BDD] -> [BDD]
    forwardR [ss] = [chooseState' (sStateVars s) ss]
    forwardR (ss:ss':p) =
      let ss0 = chooseState' (sStateVars s) ss
       in ss0 : forwardR ((ss' /\ rename subCforS (rel_product groupC ss0 (dTr dyn))) : p)

    showState :: BDD -> IO ()
    showState st = putStrLn $ show probes
      where
        rProbe (obsID, (_, obsRenderFn)) =
          text (obsID ++ ":") <+> renderFn obsRenderFn st

        probes = hsep $ map rProbe $ Map.toList (dProbes dyn)
