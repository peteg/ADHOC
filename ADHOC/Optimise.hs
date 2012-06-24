{-# LANGUAGE GADTs, TypeFamilies #-}
{- Constant propagation.
 - Copyright   :  (C)opyright 2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)

Difficult to do Arithmetic completely parametrically. Just handle
Nat for now.

 -}
module ADHOC.Optimise ( ArrowOpt, runOpt ) where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude hiding ( id, (.) )
import Control.Arrow.Transformer
import Test.QuickCheck ( Arbitrary(..) )

import ADHOC.Circuits
import ADHOC.Control.Kesterel.Kernel
import ADHOC.Data.Arithmetic
import ADHOC.Model
import ADHOC.NonDet
import ADHOC.Data.SizedLists ( mapSL )

-------------------------------------------------------------------
-- Optimiser.
-------------------------------------------------------------------

-- newtype ArrowOpt (~>) b c = ArrowOpt { unArrowOpt :: OptCompose (OptComposeID (~>)) b c }
--   deriving (Arrow, ArrowLoop, Category)
-- deriving fails for: ArrowTransformer, ArrowComb, ArrowCombLoop, ArrowDelay, ...

type ArrowOpt (~>) b c = OptCompose (OptComposeID (~>)) b c

runOpt :: Arrow (~>) => ArrowOpt (~>) b c -> b ~> c
runOpt = runOptComposeID . runOptCompose -- . unArrowOpt

-------------------------------------------------------------------
-- Hughes-style "deepen (>>>)" optimisation.
-- Use composition in the underlying Arrow when possible.
-------------------------------------------------------------------

-- | An existential type.
data OptCompose (~>) :: * -> * -> * where
  Carr :: (a -> b) -> OptCompose (~>) a b
  Cala :: (a -> b) -> (b ~> c) -> (c -> d) -> OptCompose (~>) a d

instance Arrow (~>) => Category (OptCompose (~>)) where
  id = Carr id
  Carr f . Carr g = Carr (f . g)
  Carr f . Cala pre g post = Cala pre g (f . post)
  Cala pre f post . Carr g = Cala (pre . g) f post
  Cala pre f post . Cala pre' g post' = Cala pre' (f . arr (pre . post') . g) post

instance Arrow (~>) => Arrow (OptCompose (~>)) where
  arr = Carr
  first (Carr f) = Carr (first f)
  first (Cala pre f post) = Cala (first pre) (first f) (first post)

-- FIXME seems like a capitulation.
instance ArrowLoop (~>) => ArrowLoop (OptCompose (~>)) where
  loop (Carr f) = Carr (loop f)
  loop (Cala pre f post) = Cala id (loop (arr pre >>> f >>> arr post)) id

instance Arrow (~>) => ArrowTransformer OptCompose (~>) where
  lift f = Cala id f id

instance ArrowComb (~>) => ArrowComb (OptCompose (~>)) where
  type B (OptCompose (~>)) = B (~>)

  falseA = lift falseA
  trueA = lift trueA
  andA = lift andA
  notA = lift notA
  nandA = lift nandA
  orA = lift orA
  xorA = lift xorA
  iffA = lift iffA
  impA = lift impA
  note l = lift . note l . runOptCompose

instance ArrowDelay (~>) v => ArrowDelay (OptCompose (~>)) v where
  delayA = lift delayA

-- FIXME same problem as ArrowLoop but worse
-- We don't expect (->) to have an instance of ArrowCombLoop.
instance ArrowCombLoop (~>) r => ArrowCombLoop (OptCompose (~>)) r where
  combLoop (Carr f) = Cala id (combLoop (arr f)) id
  combLoop (Cala pre f post) = Cala id (combLoop (arr pre >>> f >>> arr post)) id

instance ArrowInit (~>) => ArrowInit (OptCompose (~>)) where
  isInitialState = lift isInitialState

instance ArrowUnsafeNonDet (~>) v => ArrowUnsafeNonDet (OptCompose (~>)) v where
  unsafeNonDetInstAC p = lift (unsafeNonDetInstAC (runOptCompose p))
  unsafeNonDetAC p s = lift (unsafeNonDetAC (runOptCompose p) (runOptCompose s))

instance ArrowNonDet (~>) v => ArrowNonDet (OptCompose (~>)) v where
  nondetA = lift nondetA
  nondetFairA = lift nondetFairA

instance ArrowProbe (~>) v => ArrowProbe (OptCompose (~>)) v where
  probeA l = lift (probeA l)

instance EC (~>) => EC (OptCompose (~>))

instance (Arrow (~>), ArrowAgent (~>) obs)
       => ArrowAgent (OptCompose (~>)) obs where
  agent aid = lift . agent aid . runOptCompose

instance (Arrow (~>), ArrowBroadcast (~>) iobs cobs)
       => ArrowBroadcast (OptCompose (~>)) iobs cobs where
  broadcast agents ienvA cobsA = lift $
    broadcast (mapSL (\(aid, iobsA, fA) -> (aid, runOptCompose iobsA, runOptCompose fA)) agents)
              (runOptCompose ienvA)
              (runOptCompose cobsA)

instance (Arrow (~>), ArrowKTest (~>)) => ArrowKTest (OptCompose (~>)) where
  kTest kf = lift (kTest kf)

-- Arithmetic
data instance Nat (OptCompose (~>)) w = NatOptCompose { unNatOptCompose :: Nat (~>) w }

liftNatOC2 :: ArrowTransformer f (~>)
           => (Nat (~>) w, Nat (~>) w) ~> c
           -> f (~>) (Nat (OptCompose (~>)) w, Nat (OptCompose (~>)) w) c
liftNatOC2 f = arr unNatOptCompose *** arr unNatOptCompose >>> lift f

instance (StructureDest s (Nat (~>) w)) => StructureDest s (Nat (OptCompose (~>)) w) where
  destructure = destructure . unNatOptCompose

instance (Structure s (Nat (~>) w)) => Structure s (Nat (OptCompose (~>)) w) where
  type SIwidth s (Nat (OptCompose (~>)) w) = SIwidth s (Nat (~>) w)
  structure = NatOptCompose <$> structure

instance ArrowEq (~>) (Nat (~>) w) => ArrowEq (OptCompose (~>)) (Nat (OptCompose (~>)) w) where
  eqA = arr unNatOptCompose *** arr unNatOptCompose >>> lift eqA

instance ArrowOrd (~>) (Nat (~>) w) => ArrowOrd (OptCompose (~>)) (Nat (OptCompose (~>)) w) where
  geA = liftNatOC2 geA
  gtA = liftNatOC2 gtA
  leA = liftNatOC2 leA
  ltA = liftNatOC2 ltA

-- FIXME MulOut here, a bit of a hack.
instance ArrowNum (~>) (Nat (~>) w) => ArrowNum (OptCompose (~>)) (Nat (OptCompose (~>)) w) where
  type MulOut (OptCompose (~>)) (Nat (OptCompose (~>)) w) = MulOut (~>) (Nat (~>) w)
  addA = liftNatOC2 addA >>> arr NatOptCompose
  subA = liftNatOC2 subA >>> arr NatOptCompose
  mulA = liftNatOC2 mulA
  fromIntegerA n = lift (fromIntegerA n) >>> arr NatOptCompose

instance Show (Nat (~>) w) => Show (Nat (OptCompose (~>)) w) where
  show = unNatOptCompose >>> show

instance Eq (Nat (~>) w) => Eq (Nat (OptCompose (~>)) w) where
  NatOptCompose x == NatOptCompose y = x == y

instance Num (Nat (~>) w) => Num (Nat (OptCompose (~>)) w) where
  (+) = curry (unNatOptCompose *** unNatOptCompose >>> uncurry (+) >>> arr NatOptCompose)
  (-) = curry (unNatOptCompose *** unNatOptCompose >>> uncurry (-) >>> arr NatOptCompose)
  (*) = curry (unNatOptCompose *** unNatOptCompose >>> uncurry (*) >>> arr NatOptCompose)
  signum = unNatOptCompose >>> signum >>> NatOptCompose
  abs = unNatOptCompose >>> abs >>> NatOptCompose
  fromInteger = NatOptCompose . fromInteger

instance Ord (Nat (~>) w) => Ord (Nat (OptCompose (~>)) w) where
  compare (NatOptCompose x) (NatOptCompose y) = compare x y

instance Arbitrary (Nat (~>) w) => Arbitrary (Nat (OptCompose (~>)) w) where
  arbitrary = fmap NatOptCompose arbitrary

runOptCompose :: Arrow (~>) => OptCompose (~>) a b -> a ~> b
runOptCompose rA = case rA of
  Carr f -> arr f
  Cala pre f post -> arr pre >>> f >>> arr post

-------------------------------------------------------------------
-- Hughes-suggested composition-with-identity optimisation.
-------------------------------------------------------------------

-- | A standard ADT.
data OptComposeID (~>) :: * -> * -> * where
  CIid :: OptComposeID (~>) a a
  CIlift :: (a ~> b) -> OptComposeID (~>) a b

instance Arrow (~>) => Category (OptComposeID (~>)) where
  id = CIid
  f . CIid = f
  CIid . f = f
  CIlift f . CIlift g = CIlift (f . g)

instance Arrow (~>) => Arrow (OptComposeID (~>)) where
  arr = CIlift . arr
  first CIid = CIid
  first (CIlift f) = CIlift (first f)

instance ArrowLoop (~>) => ArrowLoop (OptComposeID (~>)) where
  loop CIid = CIid
  loop (CIlift f) = CIlift (loop f)

instance Arrow (~>) => ArrowTransformer OptComposeID (~>) where
  lift = CIlift

instance ArrowComb (~>) => ArrowComb (OptComposeID (~>)) where
  type B (OptComposeID (~>)) = B (~>)

  falseA = lift falseA
  trueA = lift trueA
  andA = lift andA
  notA = lift notA
  nandA = lift nandA
  orA = lift orA
  xorA = lift xorA
  iffA = lift iffA
  impA = lift impA
  note l = lift . note l . runOptComposeID

instance ArrowDelay (~>) v => ArrowDelay (OptComposeID (~>)) v where
  delayA = lift delayA

instance ArrowCombLoop (~>) r => ArrowCombLoop (OptComposeID (~>)) r where
  combLoop CIid = CIid
  combLoop (CIlift f) = CIlift (combLoop f)

instance ArrowInit (~>) => ArrowInit (OptComposeID (~>)) where
  isInitialState = lift isInitialState

instance ArrowUnsafeNonDet (~>) v => ArrowUnsafeNonDet (OptComposeID (~>)) v where
  unsafeNonDetInstAC p = lift (unsafeNonDetInstAC (runOptComposeID p))
  unsafeNonDetAC p s = lift (unsafeNonDetAC (runOptComposeID p) (runOptComposeID s))

instance ArrowNonDet (~>) v => ArrowNonDet (OptComposeID (~>)) v where
  nondetA = lift nondetA
  nondetFairA = lift nondetFairA

instance ArrowProbe (~>) v => ArrowProbe (OptComposeID (~>)) v where
  probeA l = lift (probeA l)

instance EC (~>) => EC (OptComposeID (~>))

instance (Arrow (~>), ArrowAgent (~>) obs)
       => ArrowAgent (OptComposeID (~>)) obs where
  agent aid = lift . agent aid . runOptComposeID

instance (Arrow (~>), ArrowBroadcast (~>) iobs cobs)
       => ArrowBroadcast (OptComposeID (~>)) iobs cobs where
  broadcast agents ienvA cobsA = lift $
    broadcast (mapSL (\(aid, iobsA, fA) -> (aid, runOptComposeID iobsA, runOptComposeID fA)) agents)
              (runOptComposeID ienvA)
              (runOptComposeID cobsA)

instance (Arrow (~>), ArrowKTest (~>)) => ArrowKTest (OptComposeID (~>)) where
  kTest kf = lift (kTest kf)

-- Arithmetic
data instance Nat (OptComposeID (~>)) w = NatOptComposeID { unNatOptComposeID :: Nat (~>) w }

liftNatOCID2 :: ArrowTransformer f (~>)
             => (Nat (~>) w, Nat (~>) w) ~> c
             -> f (~>) (Nat (OptComposeID (~>)) w, Nat (OptComposeID (~>)) w) c
liftNatOCID2 f = arr unNatOptComposeID *** arr unNatOptComposeID >>> lift f

instance (StructureDest s (Nat (~>) w)) => StructureDest s (Nat (OptComposeID (~>)) w) where
  destructure = destructure . unNatOptComposeID

instance (Structure s (Nat (~>) w)) => Structure s (Nat (OptComposeID (~>)) w) where
  type SIwidth s (Nat (OptComposeID (~>)) w) = SIwidth s (Nat (~>) w)
  structure = NatOptComposeID <$> structure

instance ArrowEq (~>) (Nat (~>) w) => ArrowEq (OptComposeID (~>)) (Nat (OptComposeID (~>)) w) where
  eqA = liftNatOCID2 eqA

instance ArrowOrd (~>) (Nat (~>) w) => ArrowOrd (OptComposeID (~>)) (Nat (OptComposeID (~>)) w) where
  geA = liftNatOCID2 geA
  gtA = liftNatOCID2 gtA
  leA = liftNatOCID2 leA
  ltA = liftNatOCID2 ltA

-- FIXME MulOut here, a bit of a hack.
instance ArrowNum (~>) (Nat (~>) w) => ArrowNum (OptComposeID (~>)) (Nat (OptComposeID (~>)) w) where
  type MulOut (OptComposeID (~>)) (Nat (OptComposeID (~>)) w) = MulOut (~>) (Nat (~>) w)
  addA = liftNatOCID2 addA >>> arr NatOptComposeID
  subA = liftNatOCID2 subA >>> arr NatOptComposeID
  mulA = liftNatOCID2 mulA
  fromIntegerA n = lift (fromIntegerA n) >>> arr NatOptComposeID

instance Show (Nat (~>) w) => Show (Nat (OptComposeID (~>)) w) where
  show = unNatOptComposeID >>> show

instance Eq (Nat (~>) w) => Eq (Nat (OptComposeID (~>)) w) where
  NatOptComposeID x == NatOptComposeID y = x == y

instance Num (Nat (~>) w) => Num (Nat (OptComposeID (~>)) w) where
  (+) = curry (unNatOptComposeID *** unNatOptComposeID >>> uncurry (+) >>> arr NatOptComposeID)
  (-) = curry (unNatOptComposeID *** unNatOptComposeID >>> uncurry (-) >>> arr NatOptComposeID)
  (*) = curry (unNatOptComposeID *** unNatOptComposeID >>> uncurry (*) >>> arr NatOptComposeID)
  signum = unNatOptComposeID >>> signum >>> NatOptComposeID
  abs = unNatOptComposeID >>> abs >>> NatOptComposeID
  fromInteger = NatOptComposeID . fromInteger

instance Ord (Nat (~>) w) => Ord (Nat (OptComposeID (~>)) w) where
  compare (NatOptComposeID x) (NatOptComposeID y) = compare x y

instance Arbitrary (Nat (~>) w) => Arbitrary (Nat (OptComposeID (~>)) w) where
  arbitrary = fmap NatOptComposeID arbitrary

runOptComposeID :: Arrow (~>) => OptComposeID (~>) a b -> a ~> b
runOptComposeID rA = case rA of
  CIid -> id
  CIlift f -> f
