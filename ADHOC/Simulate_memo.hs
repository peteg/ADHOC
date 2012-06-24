{-# LANGUAGE TypeFamilies #-}
{- In-Haskell simulator for synchronous circuits.
 - Copyright   :  (C)opyright 2004-2005, 2009-2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -
 - Caspi/Pouzet-inspired co-iterative streams.
 -
 - The setup here allows "circuits" with unbounded storage, as the
 - delay element is fully polymorphic.
 -}
module ADHOC.Simulate
    ( SyncFun
    , runSyncFun
    , sim
    , simulate, simulateBits

    , Fix(..)

    , SimBool
    , SimBoolDef(..)
    ) where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude hiding ( id, (.) )

import Test.QuickCheck	( Arbitrary(..), elements )

import ADHOC.Circuits
import ADHOC.Model	( ArrowProbe(..) )

import ADHOC.Control.Kesterel.Kernel ( EC )

-------------------------------------------------------------------
-- Fixpoints.
-------------------------------------------------------------------

-- | Types in "Fix" support the explicit computation of fixpoints.
class Fix v where
  bottom :: v

instance Fix () where bottom = ()
instance (Fix a, Fix b) => Fix (a, b) where bottom = (bottom, bottom)
instance (Fix a, Fix b, Fix c) => Fix (a, b, c) where bottom = (bottom, bottom, bottom)
instance (Fix a, Fix b, Fix c, Fix d) => Fix (a, b, c, d) where bottom = (bottom, bottom, bottom, bottom)

-------------------------------------------------------------------
-- States.
-------------------------------------------------------------------

-- | A state: either arbitrary or nothing.
data State s = Empty | State s
               deriving (Eq, Show)

state :: a -> (s -> a) -> State s -> a
state e f st = case st of
                 Empty   -> e
                 State s -> f s

-------------------------------------------------------------------
-- A (flat) 'Boolean' domain.
-------------------------------------------------------------------

-- | We simulate on the flat domain of booleans, in order to support
-- cyclic circuits.
data SimBool = SBbot | SBfalse | SBtrue
               deriving (Bounded, Enum, Eq)

instance Fix SimBool where
  bottom = SBbot

instance Show SimBool where
  show x =
    case x of
      SBbot   -> "_|_"
      SBfalse -> "false"
      SBtrue  -> "true"

instance Arbitrary SimBool where
  arbitrary = elements [minBound .. maxBound]

-- | A type of "well-defined" 'SimBool' values, so we can write QuickCheck properties.
newtype SimBoolDef = SimBoolDef { unSimBoolDef :: SimBool }

instance Show SimBoolDef where
  show = show . unSimBoolDef

instance Arbitrary SimBoolDef where
  arbitrary = elements [SimBoolDef SBfalse, SimBoolDef SBtrue]

-- | Equip them with the standard Boolean interface.
--
-- Wrinkle here: we use the parallel-and semantics.
instance Boolean SimBool where
  false = SBfalse
  true  = SBtrue

  x /\ y =
      case (x, y) of
        (SBfalse, _) -> false
        (_, SBfalse) -> false
        (SBtrue, SBtrue) -> true
        _ -> bottom

  neg x =
      case x of
        SBbot   -> bottom
        SBfalse -> true
        SBtrue  -> false

-------------------------------------------------------------------
-- Synchronous circuit arrows.
-------------------------------------------------------------------

-- | @SyncFun@s are synchronous stream functions. We maintain two
-- states: instantaneous combinational loop fixed-point state, and the
-- contents of the delays. We also track whether a fixed-point
-- computation has yielded a new (refined) value.
--
-- We manipulate the state in ways that are easier to do explicitly,
-- rather than with "StateArrow".
--
-- To be an "ArrowTransformer", the underlying "Arrow" type must come
-- last.
data SyncFun detail (~>) b c =
  forall cls ds. SyncFun ((State cls, State ds, b) ~> (Bool, State cls, State ds, c))

-- | Lift up computations in the underlying arrow.
instance Arrow (~>) => ArrowTransformer (SyncFun detail) (~>) where
  {-# SPECIALIZE instance ArrowTransformer (SyncFun detail) (->) #-}
  {-# SPECIALIZE instance ArrowTransformer (SyncFun detail) (Kleisli IO) #-}
  lift f = SyncFun $ proc (cls, ds, b) ->
    do c <- f -< b
       returnA -< (False, cls, ds, c)

instance Arrow (~>) => Category (SyncFun detail (~>)) where
  {-# SPECIALIZE instance Category (SyncFun detail (->)) #-}
  {-# SPECIALIZE instance Category (SyncFun detail (Kleisli IO)) #-}
  id = lift id
  (SyncFun g) . (SyncFun f) = SyncFun $ proc (cls, ds, b) ->
    do let (clsf, clsg) = state (Empty, Empty) id cls
           (dsf, dsg) = state (Empty, Empty) id ds
       (fc, clsf', dsf', c) <- f -< (clsf, dsf, b)
       (gc, clsg', dsg', d) <- g -< (clsg, dsg, c)
       returnA -< (fc || gc, State (clsf', clsg'), State (dsf', dsg'), d)

instance Arrow (~>) => Arrow (SyncFun detail (~>)) where
  {-# SPECIALIZE instance Arrow (SyncFun detail (->)) #-}
  {-# SPECIALIZE instance Arrow (SyncFun detail (Kleisli IO)) #-}
  arr = lift . arr
  first (SyncFun f) = SyncFun $ proc (cls, ds, (b, d)) ->
    do let (clsf, clsg) = state (Empty, Empty) id cls
           (dsf, dsg) = state (Empty, Empty) id ds
       (fc, clsf', dsf', c) <- f -< (clsf, dsf, b)
       returnA -< (fc, State (clsf', clsg), State (dsf', dsg), (c, d))

-- | Non-instantaneous stream recursion. This just hoists up the
-- underlying "ArrowLoop" instance.
instance ArrowLoop (~>) => ArrowLoop (SyncFun detail (~>)) where
  {-# SPECIALIZE instance ArrowLoop (SyncFun detail (->)) #-}
  {-# SPECIALIZE instance ArrowLoop (SyncFun detail (Kleisli IO)) #-}
  loop (SyncFun f) = SyncFun $ proc (cls, ds, b) ->
    do rec (fc, cls', ds', ~(c, d)) <- f -< (cls, ds, (b, d))
       returnA -< (fc, cls', ds', c)

-- Instances for circuits.

instance Arrow (~>) => ArrowComb (SyncFun detail (~>)) where
  {-# SPECIALIZE instance ArrowComb (SyncFun detail (->)) #-}
  {-# SPECIALIZE instance ArrowComb (SyncFun detail (Kleisli IO)) #-}
  type B (SyncFun detail (~>)) = SimBool

  falseA = arr (const false)
  trueA = arr (const true)

  andA = arr2 (/\)
  notA = arr neg

-- | We can handle all flat pointed domains uniformly.
instance (Arrow (~>), Fix v) => ArrowMux (SyncFun detail (~>)) v where
  {-# SPECIALIZE instance Fix v => ArrowMux (SyncFun detail (->)) v #-}
  {-# SPECIALIZE instance Fix v => ArrowMux (SyncFun detail (Kleisli IO)) v #-}
  muxA = proc (sel, (v0, v1)) ->
    do returnA -< case sel of
         SBbot   -> bottom
         SBfalse -> v1
         SBtrue  -> v0

-- | Initialised-by-an-'Arrow' delay. This is more useful than
-- 'sf_pre' if we represent constants as 'Arrow's and not Haskell
-- values.
--
-- We would like to use 'ArrowChoice' here to gain some effiency, but
-- with it we lose the circuit semantics when the initialiser contains
-- state itself and we have a @reset@ operation. Also this is not so
-- obviously possible with 'ArrowCombLoop'.
instance ArrowChoice (~>) => ArrowDelay (SyncFun detail (~>)) v where
  {-# SPECIALIZE instance ArrowDelay (SyncFun detail (->)) v #-}
  {-# SPECIALIZE instance ArrowDelay (SyncFun detail (Kleisli IO)) v #-}
  delayA = SyncFun $ arr $ \(cls, ds, (v0, v)) -> (False, cls, State v, state v0 id ds)

instance ArrowChoice (~>) => ArrowInit (SyncFun detail (~>)) where
    isInitialState = delayAC trueA falseA

-- | Instantaneous recursion (for cyclic circuits). This is where we
-- make essential use of the representation: we need to hold the state
-- of the delays constant while iterating the combinational loop.
--
-- Note that any effects /f/ has will be performed once for each
-- iteration of the fixpoint computation.
instance (ArrowChoice (~>), Fix v, Eq v) => ArrowCombLoop (SyncFun detail (~>)) v where
  {-# SPECIALIZE instance (Eq v, Fix v) => ArrowCombLoop (SyncFun detail (->)) v #-}
  {-# SPECIALIZE instance (Eq v, Fix v) => ArrowCombLoop (SyncFun detail (Kleisli IO)) v #-}
  combLoop (SyncFun f) = SyncFun $ proc (cls, ds, b) ->
    do let (clsf, clsI) = state (bottom, Empty) id cls
       loopf -< (False, clsI, ds, (b, clsf))
    where
      loopf = proc (fc, clsI, ds, (b, clsf)) ->
        do (fc', clsI', ds', (c, clsf')) <- f -< (clsI, ds, (b, clsf))
           if not fc' && clsf == clsf'
             then returnA -< (fc, State (clsf', clsI'), ds', c)
             else loopf -< (True, clsI', ds, (b, clsf'))

-- | Ignore probes if 'simulate'ing.
instance ArrowProbe (SyncFun detail (->)) v

-- | For 'IO' we immediately print probe values. The output is not
-- especially readable.
instance Show v => ArrowProbe (SyncFun detail (Kleisli IO)) v where
  probeA label = proc x ->
    do lift (Kleisli putStrLn) -< (showString label . showString " = " . shows x) ""
       returnA -< x

----------------------------------------

instance (ArrowLoop (~>), ArrowChoice (~>)) => EC (SyncFun detail (~>))

-- | Turn a "SyncFun" into an arrow over lazy lists. Using "Stream"
-- here implies we would need another function for the (common) finite
-- case.
runSyncFun :: ArrowChoice (~>)
           => SyncFun detail (~>) (e, b) c -> ((e, [b]) ~> [c])
runSyncFun (SyncFun f) = arr (\x -> (Empty, x)) >>> run'
  where
    run' = proc (ds, (e, xxs)) ->
      case xxs of
        []   -> returnA -< []
        x:xs -> do (_, _, ds', c) <- f -< (Empty, ds, (e, x))
                   cs <- run' -< (ds', (e, xs))
                   returnA -< c:cs

-- | Simple pure simulation.
simulate :: SyncFun ArchView (->) b c -> [b] -> [c]
simulate f xs = runSyncFun (arr snd >>> f) ((), xs)

-- | Simple pure simulation at the bit level.
simulateBits :: SyncFun BitView (->) b c -> [b] -> [c]
simulateBits f xs = runSyncFun (arr snd >>> f) ((), xs)

-- | A user-at-the-GHCi-prompt friendly simulation function.
sim :: SyncFun ArchView (Kleisli IO) b c -> [b] -> IO [c]
sim f xs = runKleisli (runSyncFun (arr snd >>> f)) ((), xs)
