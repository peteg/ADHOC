{- The interface between "ADHOC.Constructivity" and the
 - model checking / synthesis algorithms.
 - Copyright   :  (C)opyright 2006, 2009 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -}
{-# LANGUAGE TypeFamilies #-}
module ADHOC.Model
    ( ArrowAgent(..)
    , ArrowKTest(..)
    , ArrowBroadcast(..)

    , CBool(..) -- This must be abstracted in "user" code.
    , chooseState'

    , KF(..), knows, knows_hat, cknows, cknows_hat
    , KSem(..)
    , isSubjective, ensureSubjective
    , propSat

    , Model(..)

    , ArrowProbe(..)

    , RenderFn(..)
    , RenderInState(..)
    , nullRenderFn
    , combineRenderFns
    , nondetTrace
    , transitiveClosure
    ) where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude hiding ( id, (.) )

import Data.List ( foldl' )

import Data.Map		( Map )
import qualified Data.Map as Map

import qualified Text.PrettyPrint as PP
import Text.PrettyPrint hiding ( empty )

import ADHOC.Basis
import ADHOC.Circuits
import ADHOC.Generics
import ADHOC.Data.SizedLists

-------------------------------------------------------------------

-- | The single-rail type we associate with 'CArrow'.
--
-- The aim is that the only way to construct values of this type in
-- user code is to use the arrows provided by ADHOC. In other words,
-- @CBool@s cannot originate in pure functions.
newtype CBool = CBool { cbool2bdd :: BDD }

-- FIXME this is unsafe! Can then write a function:
-- arr (\(x, y). if show x == show y then (x, y) else (y, x))
instance Show CBool where
  show (CBool x) = show x

instance RenderInState CBool BDD where
  renderInState x = renderInState (cbool2bdd x)

instance Structure CBool CBool where
  type SIwidth CBool CBool = One
  structure = sallocSM

instance StructureDest CBool CBool where
  destructure = (:[])

-------------------------------------------------------------------

-- | Choose a state from a set of states.
-- Finds a valuation for all variables in the state vector, as compared to
-- 'satisfy', which just chooses a path through a 'BDD'.
chooseState' :: (Boolean b, Eq b) => [b] -> b -> b
chooseState' svars ss0
    | ss0 == false = false
    | otherwise = fst (foldl' cS (true, ss0) svars)
    where
      cS (valuation, ss) var =
        let val = if ss /\ var == false
                    then neg var
                    else var
            valuation' = valuation /\ val
            ss' = ss /\ val
         in valuation' `seq` ss `seq` (valuation', ss')

-------------------------------------------------------------------

-- | AST for the logic of knowledge formulas.
--
-- FIXME note there is no @KFprop@ -- we only use these formulas in
-- concert with KTest and there is no way to smuggle a run-time
-- value in -- you've got to use a probe.
--
-- FIXME improve Show instance.
data KF =
    -- Propositional core.
    KFfalse
  | KFtrue
  | KFprobe String
  | KF `KFand` KF
  | KF `KFor` KF
  | KF `KFxor` KF
  | KF `KFimplies` KF
  | KF `KFiff` KF
  | KFneg KF

    -- Knowledge operators.
  | AgentID `KFknows` KF -- ^ Agent @aid@ knows @f@
  | AgentID `KFknowsHat` ProbeID -- ^ Agent @aid@ knows the value of @pid@
  | [AgentID] `KFcommon` KF -- ^ @f@ is common knowledge amongst @{a}@
  | [AgentID] `KFcommonHat` ProbeID -- ^ Agent @aid@ knows the value of @pid@
  deriving (Eq, Show)

instance Boolean KF where
  false = KFfalse
  true  = KFtrue
  (/\) = KFand
  neg = KFneg
  (\/) = KFor
  xor = KFxor
  (-->) = KFimplies
  (<->) = KFiff

instance Probe KF where
  probe = KFprobe

knows :: AgentID -> KF -> KF
knows = KFknows

cknows :: [AgentID] -> KF -> KF
cknows = KFcommon

-- | Overload the syntax for the proposition "agent @aid@ knows the
-- value of the probe/formula @pid@/@f@".
--
-- At a binary type, we expect this equation to hold:
--
-- @knows_hat aid f = knows aid f \/ knows aid (neg f)@
class KnowsHat b where
  knows_hat :: AgentID -> b -> KF

instance KnowsHat ProbeID where
  knows_hat = KFknowsHat

-- FIXME we probably want to improve this instance.
-- instance KnowsHat KF where
--   knows_hat aid f = knows aid f \/ knows aid (neg f)

-- | Overload the syntax for the proposition "it is common knowledge
-- amonst @aids@ the value of the probe/formula  @pid@/@f@".
--
-- At a binary type, we expect this equation to hold:
--
-- @cknows_hat aids f = cknows aids f \/ cknows aids (neg f)@
class CKnowsHat b where
  cknows_hat :: [AgentID] -> b -> KF

instance CKnowsHat ProbeID where
  cknows_hat = KFcommonHat

-- FIXME we probably want to improve this instance.
-- instance CKnowsHat KF where
--   cknows_hat aids f = cknows aids f \/ cknows aids (neg f)

-- | Knowledge binds tightly.
infixr 9 `knows`, `knows_hat`, `cknows`, `cknows_hat`

-------------------------------------------------------------------

-- | Ultimately we want a model over the standard "Boolean" domain.
--
-- Bang on mInit and mTr for debugging (trace) convenience.
data Model b =
    Model
    { mSchedFairVars :: [b]
      -- ^ Variables used for fair scheduling / non-determinism.
      -- These are "outputs" that should have the LTL fairness constraints:
      -- /G F schedVar /\ G F (neg schedVar)/
      -- applied to them.
    , mStateVars   :: [b] -- ^ Current-state variables
    , mStateVars'  :: [b] -- ^ Successor-state variables
    , mTmpVars  :: [[b]] -- ^ \"Temporary\" state variables
    , mInitStates :: !b -- ^ Set of initial states over 'mStateVars'
    , mTr :: !b -- ^ Transition relation

    , mAgents :: [(AgentID, ([b], RenderFn b))] -- ^ Agent observations and a function to render them
    , mCommonObs :: Maybe ([b], RenderFn b) -- ^ The common observation of all the agents and a function to render it
    , mKconds :: [(AgentID, (KF, (b, b)))] -- ^ Knowledge conditions, possibly more than one per agent
    , mProbes :: Map ProbeID ([b], RenderFn b) -- ^ Probes
    } deriving Show

----------------------------------------------------------------------
-- Meta-circuits.
----------------------------------------------------------------------

-- | Probes: named signals of type @v@. Can later be used in 'KF' and
-- 'CTL' formulas.
class Arrow (~>) => ArrowProbe (~>) v where
  probeA :: ProbeID -> (v ~> v)
  probeA _ = id

----------------------------------------------------------------------

-- | Checks that the given formula is subjective to the given
-- 'AgentID', i.e. that it is a boolean combination of
-- 'AgentID'-knowledge formulas.
isSubjective :: AgentID -> KF -> Bool
isSubjective aid f0 = go f0
  where
    go f =
      case f of
        KFfalse -> True
        KFtrue -> True
        KFprobe {} -> False
        f1 `KFand` f2 -> go f1 && go f2
        f1 `KFor` f2 -> go f1 && go f2
        f1 `KFxor` f2 -> go f1 && go f2
        f1 `KFimplies` f2 -> go f1 && go f2
        f1 `KFiff` f2 -> go f1 && go f2
        KFneg f1 -> go f1

        KFknows aid' _ -> aid == aid'
        KFknowsHat aid' _ -> aid == aid'
        KFcommon aids _ -> aid `elem` aids
        KFcommonHat aids _ -> aid `elem` aids

-- | Ensure that the given formula 'isSubjective'.
ensureSubjective :: AgentID -> KF -> Bool
ensureSubjective aid kf
  | isSubjective aid kf = True
  | otherwise = error $ "Formula '" ++ show kf ++ "' is not subjective for '" ++ aid ++ "'"

----------------------------------------------------------------------

-- | Semantics for the various knowledge operators.
data KSem b = KSem
  { ksem :: AgentID -> b -> b         -- ^ Semantics for @knows@ (knowledge of a true proposition)
  , khatsem :: AgentID -> [b] -> b    -- ^ Semantics for @knows_hat@ (knowledge of a value)
  , cksem :: [AgentID] -> b -> b      -- ^ Semantics for @cknows@ (common knowledge)
  , ckhatsem :: [AgentID] -> [b] -> b -- ^ Semantics for @cknows_hat@ (common knowledge of a value)
  }

-- | FIXME document. Propositional satisfaction using the given
-- semantics for knowledge.
propSat :: Boolean b => Model b -> KSem b -> KF -> b
propSat m sem f0 = sat' f0
  where
    lookupProbe pid =
      case Map.lookup pid (mProbes m) of
        Nothing -> error $ "Model.propSat: unknown probe '" ++ pid ++ "' in formula " ++ show f0
        Just (bs, _) -> bs

    sat' f =
      case f of
        KFfalse -> false
        KFtrue -> true
        KFprobe l ->
          case lookupProbe l of
            [b] -> b
            _ -> error $ "Model.propSat: probe '" ++ l ++ "' in formula " ++ show f0 ++ " is not binary-valued."

        f1 `KFand` f2        -> sat' f1 /\ sat' f2
        f1 `KFor`  f2        -> sat' f1 \/ sat' f2
        f1 `KFxor` f2        -> sat' f1 `xor` sat' f2
        f1 `KFimplies` f2    -> sat' f1 --> sat' f2
        f1 `KFiff` f2        -> sat' f1 <-> sat' f2
        KFneg f1             -> neg $ sat' f1

        KFknows aid f1       -> ksem sem aid (sat' f1)
        KFknowsHat aid l     -> khatsem sem aid (lookupProbe l)
        KFcommon aids f1     -> cksem sem aids (sat' f1)
        KFcommonHat aids l   -> ckhatsem sem aids (lookupProbe l)
{-# SPECIALIZE propSat :: Model BDD -> KSem BDD -> KF -> BDD #-}

----------------------------------------------------------------------

-- | The @agent@ construct: names the agent and identifies what it can
-- observe.
class ArrowAgent (~>) obs where
  agent :: AgentID -> (obs ~> action) -> (obs ~> action)

-- | Broadcast environments require the agents to make the same
-- recurring /common observation/ of the shared state. They can make
-- distinct initial observations, however.
--
-- We could use lists here, but the "ADHOC.Generics" machinery doesn't
-- work with them (their sizes are not known /a priori/). A typical
-- use is to broadcast the agents' actions, i.e. @cobs ~ SizedList size a@.
class ArrowBroadcast (~>) iobs cobs where
  broadcast :: Card size
            => SizedList size (AgentID, ienv ~> iobs, (iobs, cobs) ~> action)
            -> (env ~> ienv) -- ^ Construct the environment for the initial observations
            -> (env ~> cobs) -- ^ The recurring common observation
            -> (env ~> SizedList size action)

-- | The (optional) test for knowledge part of a KBP.
--
-- The intention is that the formula talk about @KFprobe@d
-- propositions.
class ArrowKTest (~>) where
  kTest :: KF -> (env ~> B (~>))

----------------------------------------------------------------------

-- | State rendering functions.
newtype RenderFn b = RenderFn { renderFn :: b -> Doc }

instance Monoid (RenderFn b) where
    mempty = RenderFn (const PP.empty)
    RenderFn f `mappend` RenderFn g =
        RenderFn (\b -> f b PP.<> g b)

instance Show (RenderFn b) where
  show _ = "<RenderFn>"

nullRenderFn :: RenderFn b
nullRenderFn = RenderFn (const PP.empty)

combineRenderFns :: String -> RenderFn b
                 -> String -> RenderFn b
                 -> RenderFn b
combineRenderFns l lr r rr = RenderFn $
    \s -> text l PP.<> renderFn lr s PP.<> text (' ' : r) PP.<> renderFn rr s

-- | Render a value /v/ in some set of states of type /b/.
--
-- The intention is that there is only one value for /v/ in the set
-- /b/.
class RenderInState v b where
    renderInState :: v -> RenderFn b

instance RenderInState () b where
    renderInState _ = RenderFn (const PP.empty)

-- FIXME imperfect
instance RenderInState BDD BDD where
  renderInState v = RenderFn f
    where
      f s
        |     v /\ s == s = char 'T'
        | neg v /\ s == s = char 'F'
        | otherwise       = text " *** not determined."

instance (RenderInState v0 b, RenderInState v1 b)
    => RenderInState (v0, v1) b where
    renderInState (v0, v1) = RenderFn $ \s ->
      parens $ sep $ punctuate (text ", ") $
        [ renderFn (renderInState v0) s
        , renderFn (renderInState v1) s ]

instance (RenderInState v0 b, RenderInState v1 b, RenderInState v2 b)
    => RenderInState (v0, v1, v2) b where
    renderInState (v0, v1, v2) = RenderFn $ \s ->
      parens $ sep $ punctuate (text ", ") $
        [ renderFn (renderInState v0) s
        , renderFn (renderInState v1) s
        , renderFn (renderInState v2) s ]

instance (RenderInState v0 b, RenderInState v1 b, RenderInState v2 b, RenderInState v3 b)
    => RenderInState (v0, v1, v2, v3) b where
    renderInState (v0, v1, v2, v3) = RenderFn $ \s ->
      parens $ sep $ punctuate (text ", ") $
        [ renderFn (renderInState v0) s
        , renderFn (renderInState v1) s
        , renderFn (renderInState v2) s
        , renderFn (renderInState v3) s ]

instance (RenderInState v0 b, RenderInState v1 b, RenderInState v2 b, RenderInState v3 b, RenderInState v4 b)
    => RenderInState (v0, v1, v2, v3, v4) b where
    renderInState (v0, v1, v2, v3, v4) = RenderFn $ \s ->
      parens $ sep $ punctuate (text ", ") $
        [ renderFn (renderInState v0) s
        , renderFn (renderInState v1) s
        , renderFn (renderInState v2) s
        , renderFn (renderInState v3) s
        , renderFn (renderInState v4) s ]

-- FIXME here because SizedList is used in Broadcast.
instance (Card size, RenderInState a b)
      => RenderInState (SizedList size a) b where
    renderInState sl = RenderFn $ \s ->
      brackets $ sep $ punctuate (text ", ") $ map (\x -> renderFn (renderInState x) s) (unSizedListA sl)

----------------------------------------------------------------------

-- | Print a trace that ends in (at least) two successors.
nondetTrace :: Model BDD -> IO ()
nondetTrace m = forwardR (mInitStates m)
  where
    groupC = mkGroup (mStateVars m)
    subCforS = mkSubst (zip (mStateVars' m) (mStateVars m))

    isSingleton :: [BDD] -> BDD -> Bool
    isSingleton xxs ss0
      | ss0 == false = False
      | otherwise = case xxs of
          [] -> True
          x:xs -> isSingleton xs (ss0 /\ x) <-> not (isSingleton xs (ss0 /\ neg x))

    forwardR :: BDD -> IO ()
    forwardR ss0
      | isSingleton (mStateVars m) ss0 =
          do showState ss0
             putStrLn "----"
             forwardR (rename subCforS (rel_product groupC ss0 (mTr m)))
      | otherwise =
          do let s  = chooseState' (mStateVars m) ss0
                 s' = chooseState' (mStateVars m) (ss0 /\ neg s)
             putStrLn "TWO SUCCS"
             showState s
             putStrLn "===="
             showState s'

    showState :: BDD -> IO ()
    showState st = putStrLn $ show probes
      where
        rProbe (obsID, (_, obsRenderFn)) =
          text (obsID ++ ":") <+> renderFn obsRenderFn st

        probes = hsep $ map rProbe $ Map.toList (mProbes m)

-------------------------------------------------------------------

-- | Computes the transitive closure of a relation @r@:
--
-- @transitiveClosure r = 'fix' false (\r' -> r' \\\/ (rel_product zs r[zs\/ran(r)] r[zs\/(dom(r)])@
--
-- assuming that @domain@ and @range@ have the same length and @zs@
-- are fresh. We assume here the relation is over states in the model.
transitiveClosure :: BDDOps b
                  => Model b
                  -> b -- ^ @r@
                  -> b
transitiveClosure m r = fix r f
  where
    s = mStateVars m
    s' = mStateVars' m
    (t:_) = mTmpVars m

    f r' = r' \/ step
    step = rel_product (mkGroup t)
             (rename (mkSubst $ zip s' t) r)
             (rename (mkSubst $ zip s  t) r)
