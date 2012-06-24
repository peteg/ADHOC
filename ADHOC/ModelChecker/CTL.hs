{- CTL model checking, following /Model Checking/ E. Clarke, O. Grumberg, D. Peled (2000).
 - Copyright   :  (C)opyright 2006, 2009 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -
-- Issues:
--   - Fairness
--     - probably better to use the unfair operators if there are no fairness
--       constraints.
 -}
module ADHOC.ModelChecker.CTL
    (
      -- * CTL models
      CTLModel(..)
    , CTLFair(..)
    , mkCTLModel

      -- * CTL abstract syntax
    , CTL(..)
    , prop -- , probe -- Exported from ADHOC.Basis
    , ax, ex, af, ef, ag, eg, au, eu
    , au_unbounded

      -- * CTL model checking
    , CTLResult(..)
    , ufeg, ufeu, ufex
    , eg_sem, eu_sem, ex_sem
    , isOK, isFailure
    , mc
    , sat

      -- * Extra stuff
    , chooseState
    , forwardOneStep
    ) where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude hiding ( id, (.) )

import qualified Data.Map as Map

import ADHOC.Basis
import ADHOC.Model

-------------------------------------------------------------------
-- Abstract syntax.
-------------------------------------------------------------------

data CTL b =
      -- Propositional core
      CTLprop b
    | CTLprobe ProbeID

    | (CTL b) `CTLand` (CTL b)
    | (CTL b) `CTLor` (CTL b)
    | (CTL b) `CTLxor` (CTL b)
    | (CTL b) `CTLimplies` (CTL b)
    | (CTL b) `CTLiff` (CTL b)
    | CTLneg (CTL b)

      -- CTL operators
    | CTLax (CTL b)		-- ^ "/f/ in all next states"
    | CTLex (CTL b)		-- ^ "/f/ in at least one next state"
    | (CTL b)`CTLau` (CTL b)	-- ^ "on all paths, /p/ until /q/"
    | (CTL b)`CTLeu` (CTL b)	-- ^ "on at least one path, /p/ until /q/"
    | CTLaf (CTL b)		-- ^ "on all paths, in some future state, /f/"
    | CTLef (CTL b)		-- ^ "on at least one path, in some future state, /f/"
    | CTLag (CTL b)		-- ^ "on all paths, in all future states, /f/"
    | CTLeg (CTL b)		-- ^ "on at least one path, in all future states, /f/"
      -- Knowledge operators.
--     | CTLknows String (CTL b)	-- ^ agent a knows f.
--     | CTLcommon [String] (CTL	b) -- ^ /f/ is common knowledge amongst {a}.
      deriving (Eq, Show)

ax, ex, af, ef, ag, eg :: CTL b -> CTL b
au, eu :: CTL b -> CTL b -> CTL b

ax = CTLax
ex = CTLex
au = CTLau
eu = CTLeu
af = CTLaf
ef = CTLef
ag = CTLag
eg = CTLeg

-- | "unbounded" invariants -- if the eventuality isn't satisfied, the
-- invariant holds forevermore.
au_unbounded :: (Boolean b, Eq b) => CTL b -> CTL b -> CTL b
f `au_unbounded` g = neg (neg g `eu` (neg f /\ neg g))

-- FIXME maybe later.
-- knows :: String -> CTL b -> CTL b
-- knows = CTLknows

-- | Primitive propositions originating from the "Constructivity"
-- interpretation.
prop :: CBool -> CTL BDD
prop = CTLprop . cbool2bdd

-- | Primitive propositions originating from circuit probes.
instance Probe (CTL b) where
  probe = CTLprobe

-------------------------------------------------------------------
-- Boolean instances.
-------------------------------------------------------------------

instance (Boolean b, Eq b) => Boolean (CTL b) where
  false = CTLprop false
  true  = CTLprop true
  (/\) = CTLand
  neg = CTLneg
  (\/) = CTLor
  xor = CTLxor
  (-->) = CTLimplies
  (<->) = CTLiff

-------------------------------------------------------------------
-- CTL Models.
-------------------------------------------------------------------

-- | Shared state for CTL model checking.
data CTLModel b =
    CTLModel
    { ctlModel :: !(Model b)
    , ctlGroupC :: !(Group b)
    , ctlGroupS :: !(Group b)
    , ctlSubCforS :: b -> b
    , ctlSubSforC :: b -> b
    , ctlReachable :: b -- ^ Set of reachable states, for the Kobs modality.
    , ctlMFair :: Maybe (CTLFair b)
    }

-- | With fairness constraints we need extra stuff.
--
-- We probably want to be lazy in most of these fields as computing
-- them may consume huge amounts of space.
data CTLFair b =
  CTLFair
  { ctlFair :: b -- ^ Set of fair states.
  , ctlFairConstraints :: [b] -- ^ Set of fairness constraints.
  , ctlFairInit :: b -- ^ Set of initial states that lead to fair runs.
  }

-- | Construct a 'CTLModel' for the given model.
-- Careful! Note the use of laziness here (ctlFair).
mkCTLModel :: forall b. BDDOps b => Model b -> CTLModel b
mkCTLModel m
    | null (mStateVars m) = error "No states."
    | null (mSchedFairVars m) = if mInitStates m == false then error "Set of initial states is empty." else ctlM_unfair
    | otherwise = if ctlFairInit fair == false then error "Set of initial states is empty." else ctlM_fair
  where
    subCforS = rename (mkSubst (zip (mStateVars' m) (mStateVars  m)))
    subSforC = rename (mkSubst (zip (mStateVars  m) (mStateVars' m)))
    groupC = mkGroup (mStateVars  m)
    groupS = mkGroup (mStateVars' m)

    -- FIXME verify: all paths starting from the fair initial states are fair.
    -- If not, intersect the result with ctlFair
    reachableStates = fix (if null (mSchedFairVars m) then mInitStates m else ctlFairInit fair) f
      where
       f ss = assert (ss' /= false) $ ss \/ ss'
           where ss' = subCforS $ rel_product groupC ss (mTr m)

    ctlM_unfair = CTLModel { ctlModel = m
                           , ctlGroupC = groupC
                           , ctlGroupS = groupS
                           , ctlSubCforS = subCforS
                           , ctlSubSforC = subSforC
                           , ctlReachable = reachableStates
                           , ctlMFair = Nothing
                           }

    ctlM_fair :: CTLModel b
    ctlM_fair = ctlM_unfair{ ctlMFair = Just fair }

    fair :: CTLFair b
    fair = CTLFair { ctlFair = feg ctlM_fair fair true
                   , ctlFairConstraints = concat [ [ s, neg s ] | s <- mSchedFairVars m ]
                   , ctlFairInit = mInitStates m /\ ctlFair fair
                   }

----------------------------------------
-- Standard (unfair) CTL semantics.
----------------------------------------

ufex :: BDDOps b => CTLModel b -> b -> b
ufex ctlM f = rel_product (ctlGroupS ctlM) (ctlSubSforC ctlM f) (mTr (ctlModel ctlM))

ufeg :: BDDOps b => CTLModel b -> b -> b
ufeg ctlM f = fix f step
  where step ss = f /\ ufex ctlM ss

ufeu :: BDDOps b => CTLModel b -> b -> b -> b
ufeu ctlM f g = fix g step
  where step ss = g \/ (f /\ ufex ctlM ss)

----------------------------------------
-- CTL-with-fairness-constraints semantics.
----------------------------------------

fex :: BDDOps b => CTLModel b -> CTLFair b -> b -> b
fex ctlM ctlF f0 = ufex ctlM (f0 /\ ctlFair ctlF)

feg :: BDDOps b => CTLModel b -> CTLFair b -> b -> b
feg ctlM ctlF f0 =
    let f ss = f0 /\ conjoin [ ufex ctlM (ufeu ctlM f0 (ss /\ hk))
                             | hk <- ctlFairConstraints ctlF ]
     in fix f0 f

feu :: BDDOps b => CTLModel b -> CTLFair b -> b -> b -> b
feu ctlM ctlF f1 f2 = ufeu ctlM f1 (f2 /\ ctlFair ctlF)

-------------------------------------------------------------------
-- Semantics (fair or unfair, depending) for CTL operators.
-------------------------------------------------------------------

ufORf :: CTLModel b -> (CTLModel b -> a) -> (CTLModel b -> CTLFair b -> a) -> a
ufORf ctlM x y = maybe (x ctlM) (y ctlM) (ctlMFair ctlM)

ax_sem :: BDDOps b => CTLModel b -> b -> b
ax_sem ctlM = neg . ex_sem ctlM . neg

ex_sem :: BDDOps b => CTLModel b -> b -> b
ex_sem ctlM = ufORf ctlM ufex fex

af_sem :: BDDOps b => CTLModel b -> b -> b
af_sem ctlM = neg . eg_sem ctlM . neg

ef_sem :: BDDOps b => CTLModel b -> b -> b
ef_sem ctlM = ufORf ctlM ufeu feu true

ag_sem :: BDDOps b => CTLModel b -> b -> b
ag_sem ctlM = neg . ef_sem ctlM . neg

eg_sem :: BDDOps b => CTLModel b -> b -> b
eg_sem ctlM = ufORf ctlM ufeg feg

au_sem :: BDDOps b => CTLModel b -> b -> b -> b
au_sem ctlM f g = neg (eu_sem ctlM (neg g) (neg f /\ neg g)) /\ neg (eg_sem ctlM (neg g))

eu_sem :: BDDOps b => CTLModel b -> b -> b -> b
eu_sem ctlM = ufORf ctlM ufeu feu

-------------------------------------------------------------------
-- CTL Model Checking.
-------------------------------------------------------------------

data CTLResult b = CTLok | CTLfailure { ctlFailingStates :: b }
                   deriving Show

isOK :: CTLResult b -> Bool
isOK CTLok = True
isOK _     = False

isFailure :: CTLResult b -> Bool
isFailure (CTLfailure {}) = True
isFailure _               = False

-- | Check that the given model satisfies the given formula using the
-- fair CTL semantics.
mc :: (BDDOps b, Show b) => CTLModel b -> CTL b -> CTLResult b
mc ctlM f
    | failingStates == false = CTLok
    | otherwise = CTLfailure failingStates
  where
    failingStates = neg (sat ctlM f) /\ ufORf ctlM (mInitStates . ctlModel) (const ctlFairInit)

-- | Yields the set of states where the CTL formula holds in the given
-- model.
sat :: (BDDOps b, Show b) => CTLModel b -> CTL b -> b
sat ctlM f0 = sat' f0
  where
    sat' f =
      case f of
        -- Propositional core.
        CTLprop p -> p
        CTLprobe l ->
          case Map.lookup l (mProbes (ctlModel ctlM)) of
            Nothing -> error $ "CTL.sat: unknown probe '" ++ l ++ "' in formula " ++ show f0
            Just ([b], _) -> b
            _ -> error $ "CTL.sat: probe '" ++ l ++ "' in formula " ++ show f0 ++ " is not binary-valued."

        f1 `CTLand` f2        -> sat' f1 /\ sat' f2
        f1 `CTLor`  f2        -> sat' f1 \/ sat' f2
        f1 `CTLxor` f2        -> sat' f1 `xor` sat' f2
        f1 `CTLimplies` f2    -> sat' f1 --> sat' f2
        f1 `CTLiff` f2        -> sat' f1 <-> sat' f2
        CTLneg f1             -> neg $ sat' f1

        -- CTL
        CTLax f1        -> ax_sem ctlM (sat' f1)
        CTLex f1        -> ex_sem ctlM (sat' f1)

        CTLaf f1        -> af_sem ctlM (sat' f1)
        CTLef f1        -> ef_sem ctlM (sat' f1)

        CTLag f1        -> ag_sem ctlM (sat' f1)
        CTLeg f1        -> eg_sem ctlM (sat' f1)

        f1 `CTLau` f2   -> au_sem ctlM (sat' f1) (sat' f2)
        f1 `CTLeu` f2   -> eu_sem ctlM (sat' f1) (sat' f2)

-------------------------------------------------------------------
-- Auxiliary useful things.
-------------------------------------------------------------------

chooseState :: (Boolean b, Eq b) => CTLModel b -> b -> b
chooseState ctlM = chooseState' (mStateVars (ctlModel ctlM))

forwardOneStep :: QBF b => CTLModel b -> b -> b
forwardOneStep ctlM ss =
    ufORf ctlM (const id) (const ( (/\) . ctlFair) ) $
      ctlSubCforS ctlM $ rel_product (ctlGroupC ctlM) ss tr
  where tr = mTr (ctlModel ctlM)
