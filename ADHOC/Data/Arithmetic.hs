{-# LANGUAGE UndecidableInstances #-}
{- Fixed-size natural number arithmetic.
 - Copyright   :  (C)opyright 2006, 2009 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -}
module ADHOC.Data.Arithmetic
    ( -- * Arithmetic operations
      ArrowEq(..)
    , ArrowOrd(..)
    , ArrowNum(..)
    , ArrowNumCast(..)

      -- * Arithmetic representations
    , Nat
    , natA
    , constNatA
    , module ADHOC.Generics

      -- * Derived operations
    , eqAC
    , geAC, gtAC, leAC, ltAC
    , addAC, subAC, mulAC
    , incA
    , decA
    , maxAC, minAC

      -- * "SizedList" operations
    , isOneHotSL
    , atMostOneSL

      -- * Primitive arithmetic circuits
    , fullAdd
    ) where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude ()

import Data.List ( foldl', genericReplicate )
import Test.QuickCheck ( Arbitrary(..), choose )
import Text.PrettyPrint as PP

import ADHOC.Circuits
import ADHOC.Constructivity	( CArrow )
import ADHOC.Generics
import ADHOC.Model		( CBool, cbool2bdd, RenderInState(..), RenderFn(..) )
import ADHOC.NetList
import ADHOC.Simulate		( SyncFun, Fix(..), SimBool )
import ADHOC.Data.SizedLists	( SizedList, foldrSL )

import ADHOC.Data.ArithmeticCircuits
-- import ADHOC.Data.Patterns

-------------------------------------------------------------------
-- Classes
-------------------------------------------------------------------

-- | Equality.
class ArrowComb (~>) => ArrowEq (~>) a where
  eqA :: (a, a) ~> B (~>)

-- | Total orderings. Minimal complete definition: @leA@, @ltA@.
class ArrowEq (~>) a => ArrowOrd (~>) a where
  geA :: (a, a) ~> B (~>)
  geA = swapA >>> leA
  gtA :: (a, a) ~> B (~>)
  gtA = swapA >>> ltA

  leA :: (a, a) ~> B (~>)
  ltA :: (a, a) ~> B (~>)

-- | Basic arithmetic.
class Arrow (~>) => ArrowNum (~>) n where
  type MulOut (~>) n :: *
  addA :: (n, n) ~> n
  subA :: (n, n) ~> n

  -- | Multiplication. We allow the size of the output to depend on
  -- the size of the inputs.
  mulA :: (n, n) ~> MulOut (~>) n

  fromIntegerA :: Integer -> (env ~> n)

-- | Cast one numeric type to another.
class Arrow (~>) => ArrowNumCast (~>) ni no where
  numCastA :: ni ~> no

-- | Command combinator variants.
eqAC :: ArrowEq (~>) a => (env ~> a) -> (env ~> a) -> (env ~> B (~>))
eqAC = liftAC2 eqA

geAC, gtAC, leAC, ltAC :: ArrowOrd (~>) a => (env ~> a) -> (env ~> a) -> (env ~> B (~>))
geAC = liftAC2 geA
gtAC = liftAC2 gtA
leAC = liftAC2 leA
ltAC = liftAC2 ltA

addAC, subAC :: ArrowNum (~>) n => (env ~> n) -> (env ~> n) -> (env ~> n)
addAC = liftAC2 addA
subAC = liftAC2 subA

mulAC :: ArrowNum (~>) n => (env ~> n) -> (env ~> n) -> (env ~> MulOut (~>) n)
mulAC = liftAC2 mulA

infixl 7 `mulAC`
infixl 6 `addAC`, `subAC`
infix  4 `eqAC`, `geAC`, `gtAC`, `leAC`, `ltAC`

-------------------------------------------------------------------
-- Generic operations.
-------------------------------------------------------------------

incA :: ArrowNum (~>) n => n ~> n
incA = proc x -> addA <<< second (fromIntegerA 1) -< (x, ())

decA :: ArrowNum (~>) n => n ~> n
decA = proc x -> subA <<< second (fromIntegerA 1) -< (x, ())

minAC :: (ArrowMux (~>) n, ArrowNum (~>) n, ArrowOrd (~>) n)
      => (env ~> n) -> (env ~> n) -> (env ~> n)
minAC f g = proc env ->
  do x <- f -< env
     y <- g -< env
     (| muxAC ((returnA -< x) `leAC` (returnA -< y))
              (returnA -< x)
              (returnA -< y) |)

maxAC :: (ArrowMux (~>) n, ArrowNum (~>) n, ArrowOrd (~>) n)
      => (env ~> n) -> (env ~> n) -> (env ~> n)
maxAC f g = proc env ->
  do x <- f -< env
     y <- g -< env
     (| muxAC ((returnA -< x) `geAC` (returnA -< y))
              (returnA -< x)
              (returnA -< y) |)

-------------------------------------------------------------------
-- SizedList stuff.
-------------------------------------------------------------------

-- | Is the input 'SizedList' one-hot, i.e. does it have exactly one
-- bit set?
isOneHotSL :: (Card w, ArrowComb (~>))
           => SizedList w (B (~>)) ~> B (~>)
isOneHotSL = foldrSL f z >>> (notA *** id) >>> andA
  where
    z = falseA &&& falseA
    f = proc ((cin, y), x) ->
      do (xy, cout) <- fullAdd -< (cin, (x, y))
         orA *** id -< ((cin, cout), xy)

-- | Is at most one bit in a 'SizedList' set?
atMostOneSL :: (Card w, ArrowComb (~>))
            => SizedList w (B (~>)) ~> B (~>)
atMostOneSL = foldrSL f z >>> arr snd
  where
    z = falseA &&& trueA
    f = proc ((seenBit, out), x) ->
      do seenBit' <- orA -< (seenBit, x)
         out' <- andA <<< second nandA -< (out, (seenBit, x))
         returnA -< (seenBit', out')

-------------------------------------------------------------------
-- Common numeric types.
-------------------------------------------------------------------

-- | Saturated natural number arithmetic: @0 - x = 0@, @max + x = max@.
-- 'size' is the number of bits.
-- The arrow determines the representation.
data family Nat ((~>) :: * -> * -> *) (size :: *) :: *

natA :: (Card w, Category (~>)) => w -> Nat (~>) w ~> Nat (~>) w
natA _ = id

constNatA :: (Card w, ArrowNum (~>) (Nat (~>) w)) => w -> Integer -> (env ~> Nat (~>) w)
constNatA _ = fromIntegerA

-- This requires {-# LANGUAGE UndecidableInstances #-}
instance (Card w, ArrowNum (~>) (Nat (~>) w)) => Zero (~>) (Nat (~>) w) where
  zeroA = constNatA (undefined :: w) 0

----------------------------------------
-- 'CArrow' naturals are generic in the bit-size.
----------------------------------------

data instance Nat CArrow w = NatCArrow { unNatCArrow :: [B CArrow] }

-- This is what w ewant to say, but GHC 7.0.x won't have it:
-- instance StructureDest (B CArrow) (Nat w CArrow) where
instance Card w => StructureDest CBool (Nat CArrow w) where
  destructure = unNatCArrow

instance Card w => Structure CBool (Nat CArrow w) where
  type SIwidth CBool (Nat CArrow w) = CardMul w (SIwidth CBool (B CArrow))
  structure = NatCArrow <$> for [1..width] (const structure)
    where
      width = c2num (undefined :: w) :: Integer

instance Card w => RenderInState (Nat CArrow w) BDD where
  renderInState (NatCArrow v) = RenderFn (PP.integer . natToInteger . bits)
    where
      size = c2num (undefined :: w) :: Integer
      bits s = zipWith (/\) (genericReplicate size s) (map cbool2bdd v)
      natToInteger = foldl' (\n d -> n * 2 + if d == false then 0 else 1) (0 :: Integer)

instance Card w => ArrowEq CArrow (Nat CArrow w) where
    eqA = arr unNatCArrow *** arr unNatCArrow >>> equalA size
        where size = c2num (undefined :: w)

instance Card w => ArrowOrd CArrow (Nat CArrow w) where
    leA = arr (unNatCArrow *** unNatCArrow) >>> leNat size
        where size = c2num (undefined :: w)
    ltA = arr (unNatCArrow *** unNatCArrow) >>> ltNat size
        where size = c2num (undefined :: w)

instance Card w => ArrowNum CArrow (Nat CArrow w) where
  -- | Multiplication yields a 'Nat' twice as wide as its inputs.
  type MulOut CArrow (Nat CArrow w) = Nat CArrow (CardAdd w w)

  addA = arr (unNatCArrow *** unNatCArrow) >>> addNat size >>> arr NatCArrow
    where size = c2num (undefined :: w)

  subA = arr (unNatCArrow *** unNatCArrow) >>> subNat size >>> arr NatCArrow
    where size = c2num (undefined :: w)

  mulA = arr (unNatCArrow *** unNatCArrow) >>> mulNat size >>> arr NatCArrow
    where size = c2num (undefined :: w)

  fromIntegerA n = toNatAC size n >>> arr NatCArrow
    where size = c2num (undefined :: w)

-- | Casting is possible by truncation or adding binary zeroes on the
-- right.
instance (Card w0, Card w1) => ArrowNumCast CArrow (Nat CArrow w0) (Nat CArrow w1) where
  numCastA = arr unNatCArrow >>> castNat size0 size1 >>> arr NatCArrow
    where
      size0 = c2num (undefined :: w0)
      size1 = c2num (undefined :: w1)

----------------------------------------
-- Generic 'NLArrow' naturals.
----------------------------------------

--------------------
-- Arch-level view
-- Might still want to identify bit widths.
--------------------

data instance Nat (NLArrow ArchView) w = NatNLArrowArch { unNatNLArrowArch :: B (NLArrow ArchView) }

instance Card w => StructureDest NodeID (Nat (NLArrow ArchView) w) where
  destructure = (:[]) . unNatNLArrowArch

instance Card w => Structure NodeID (Nat (NLArrow ArchView) w) where
  type SIwidth NodeID (Nat (NLArrow ArchView) w) = SIwidth NodeID (B (NLArrow ArchView))
  structure = NatNLArrowArch <$> structure

instance ArrowEq (NLArrow ArchView) (Nat (NLArrow ArchView) w) where
    eqA = arr (unNatNLArrowArch *** unNatNLArrowArch)
            >>> mkNL2 (NodeAttr {nLabel = "eqA", nShape = Scirc}, (NoWireAttrs, NoWireAttrs))

instance ArrowOrd (NLArrow ArchView) (Nat (NLArrow ArchView) w) where
    leA = arr (unNatNLArrowArch *** unNatNLArrowArch)
            >>> mkNL2 (NodeAttr {nLabel = "leA", nShape = Scirc}, (WireAttr "l", WireAttr "r"))
    ltA = arr (unNatNLArrowArch *** unNatNLArrowArch)
            >>> mkNL2 (NodeAttr {nLabel = "ltA", nShape = Scirc}, (WireAttr "l", WireAttr "r"))

instance ArrowNum (NLArrow ArchView) (Nat (NLArrow ArchView) w) where
  type MulOut (NLArrow ArchView) (Nat (NLArrow ArchView) w) = Nat (NLArrow ArchView) (CardAdd w w)
  addA = arr (unNatNLArrowArch *** unNatNLArrowArch)
           >>> mkNL2 (NodeAttr {nLabel = "addA", nShape = Scirc}, (NoWireAttrs, NoWireAttrs))
             >>> arr NatNLArrowArch
  subA = arr (unNatNLArrowArch *** unNatNLArrowArch)
           >>> mkNL2 (NodeAttr {nLabel = "subA", nShape = Scirc}, (WireAttr "l", WireAttr "r"))
             >>> arr NatNLArrowArch
  mulA = arr (unNatNLArrowArch *** unNatNLArrowArch)
           >>> mkNL2 (NodeAttr {nLabel = "mulA", nShape = Scirc}, (NoWireAttrs, NoWireAttrs))
             >>> arr NatNLArrowArch

  fromIntegerA n = mkNL (\_ -> (NodeAttr {nLabel = show n, nShape = Sbox}, []))
                     >>> arr NatNLArrowArch

--------------------
-- Bit-level view
--------------------

data instance Nat (NLArrow BitView) w = NatNLArrowBits { unNatNLArrowBits :: [B (NLArrow BitView)] }

-- FIXME hideously concrete: we mean B (NLArrow BitView)
instance Card w => StructureDest NodeID (Nat (NLArrow BitView) w) where
  destructure = unNatNLArrowBits

instance Card w => Structure NodeID (Nat (NLArrow BitView) w) where
  type SIwidth NodeID (Nat (NLArrow BitView) w) = CardMul w (SIwidth NodeID (B (NLArrow BitView)))
  structure = NatNLArrowBits <$> for [1..width] (const structure)
    where
      width = c2num (undefined :: w) :: Integer

instance Card w => ArrowEq (NLArrow BitView) (Nat (NLArrow BitView) w) where
  eqA = arr (unNatNLArrowBits *** unNatNLArrowBits)
          >>> equalA size
    where size = c2num (undefined :: w)

instance Card w => ArrowOrd (NLArrow BitView) (Nat (NLArrow BitView) w) where
  leA = arr (unNatNLArrowBits *** unNatNLArrowBits)
          >>> leNat size
    where size = c2num (undefined :: w)
  ltA = arr (unNatNLArrowBits *** unNatNLArrowBits)
          >>> ltNat size
    where size = c2num (undefined :: w)

instance Card w => ArrowNum (NLArrow BitView) (Nat (NLArrow BitView) w) where
  type MulOut (NLArrow BitView) (Nat (NLArrow BitView) w) = Nat (NLArrow BitView) (CardAdd w w)
  addA = arr (unNatNLArrowBits *** unNatNLArrowBits)
           >>> addNat size
             >>> arr NatNLArrowBits
    where size = c2num (undefined :: w)

  subA = arr (unNatNLArrowBits *** unNatNLArrowBits)
           >>> subNat size
             >>> arr NatNLArrowBits
    where size = c2num (undefined :: w)

  mulA = arr (unNatNLArrowBits *** unNatNLArrowBits)
           >>> mulNat size
             >>> arr NatNLArrowBits
    where size = c2num (undefined :: w)

  fromIntegerA n = toNatAC size n >>> arr NatNLArrowBits
    where size = c2num (undefined :: w)

----------------------------------------
-- Generic 'SyncFun' naturals.
-- These are intended to be used for testing, so we provide
-- convenience instances for standard Haskell classes.
----------------------------------------

--------------------
-- Arch-level view
-- The presence of undefined booleans leaks into Nats due to ArrowMux.
--------------------

data instance Nat (SyncFun ArchView (~>)) w = NatSyncFunArch { unNatSyncFunArch :: Maybe Integer }

trunc :: forall w. Card w => w -> Integer -> Integer
trunc _ x = if x < 0 then 0 else if x > limit then limit else x
  where limit = 2 ^ (c2num (undefined :: w) :: Integer) - 1

-- Binary operations are strict in both arguments.
nSFAlift :: forall a (~>) wi wo. (Arrow a, Card wo)
         => (Integer -> Integer -> Integer)
         -> (Nat (SyncFun ArchView (~>)) wi, Nat (SyncFun ArchView (~>)) wi)
            `a` (Nat (SyncFun ArchView (~>))  wo)
nSFAlift f = arr ((unNatSyncFunArch *** unNatSyncFunArch) >>> f' >>> NatSyncFunArch)
  where
    f' (Just x, Just y) = Just (trunc (undefined :: wo) (f x y))
    f' _ = Nothing

instance Eq (Nat (SyncFun ArchView (~>)) w) where
  NatSyncFunArch x == NatSyncFunArch y = x == y

instance Fix (Nat (SyncFun ArchView (~>)) w) where
  bottom = NatSyncFunArch Nothing

instance Show (Nat (SyncFun ArchView (~>)) w) where
  show = show . unNatSyncFunArch

instance Card w => Num (Nat (SyncFun ArchView (~>)) w) where
  (+) = curry (nSFAlift (+))
  (-) = curry (nSFAlift (+))
  (*) = curry (nSFAlift (+))
  signum = const 1
  abs = id
  fromInteger = NatSyncFunArch . Just . trunc (undefined :: w)

instance Ord (Nat (SyncFun ArchView (~>)) w) where
  compare (NatSyncFunArch x) (NatSyncFunArch y) = compare x y

instance Card w => Arbitrary (Nat (SyncFun ArchView (~>)) w) where
  arbitrary =
    do n <- choose (0, 2 ^ (c2num (undefined :: w) :: Integer) - 1)
       return (NatSyncFunArch (Just n))

instance StructureDest (Maybe Integer) (Nat (SyncFun ArchView (~>)) w) where
  destructure = (:[]) . unNatSyncFunArch

instance Structure (Maybe Integer) (Nat (SyncFun ArchView (~>)) w) where
  type SIwidth (Maybe Integer) (Nat (SyncFun ArchView (~>)) w) = One
  structure = fmap NatSyncFunArch structure

instance Arrow (~>) => ArrowEq (SyncFun ArchView (~>)) (Nat (SyncFun ArchView (~>)) w) where
  eqA = arr (uncurry (==) >>> \b -> if b then true else false)

instance Arrow (~>) => ArrowOrd (SyncFun ArchView (~>)) (Nat (SyncFun ArchView (~>)) w) where
  leA = arr ((unNatSyncFunArch *** unNatSyncFunArch) >>> uncurry (<=) >>> \b -> if b then true else false)
  ltA = arr ((unNatSyncFunArch *** unNatSyncFunArch) >>> uncurry (<) >>> \b -> if b then true else false)

instance (Arrow (~>), Card w)
      => ArrowNum (SyncFun ArchView (~>)) (Nat (SyncFun ArchView (~>)) w) where
  type MulOut (SyncFun ArchView (~>)) (Nat (SyncFun ArchView (~>)) w) = Nat (SyncFun ArchView (~>)) (CardAdd w w)
  addA = nSFAlift (+)
  subA = nSFAlift (-)
  mulA = nSFAlift (*)

  fromIntegerA = arr . const . NatSyncFunArch . Just . fromInteger

--------------------
-- Bit-level view
--------------------

data instance Nat (SyncFun BitView (~>)) w = NatSyncFunBits { unNatSyncFunBits :: [B (SyncFun BitView (~>))] }

instance Card w => StructureDest SimBool (Nat (SyncFun BitView (~>)) w) where
  destructure = unNatSyncFunBits

instance Card w => Structure SimBool (Nat (SyncFun BitView (~>)) w) where
  type SIwidth SimBool (Nat (SyncFun BitView (~>)) w) = CardMul w (SIwidth SimBool (B (SyncFun BitView (~>))))
  structure = NatSyncFunBits <$> for [1..width] (const structure)
    where
      width = c2num (undefined :: w) :: Integer

instance (Arrow (~>), Card w) => ArrowEq (SyncFun BitView (~>)) (Nat (SyncFun BitView (~>)) w) where
  eqA = arr (unNatSyncFunBits *** unNatSyncFunBits) >>> equalA size
    where size = c2num (undefined :: w)

instance (Arrow (~>), Card w) => ArrowOrd (SyncFun BitView (~>)) (Nat (SyncFun BitView (~>)) w) where
  leA = arr (unNatSyncFunBits *** unNatSyncFunBits) >>> leNat size
    where size = c2num (undefined :: w)
  ltA = arr (unNatSyncFunBits *** unNatSyncFunBits) >>> ltNat size
    where size = c2num (undefined :: w)

instance (Arrow (~>), Card w) => ArrowNum (SyncFun BitView (~>)) (Nat (SyncFun BitView (~>)) w) where
  type MulOut (SyncFun BitView (~>)) (Nat (SyncFun BitView (~>)) w) = Nat (SyncFun BitView (~>)) (CardAdd w w)
  addA = arr (unNatSyncFunBits *** unNatSyncFunBits) >>> addNat size >>> arr NatSyncFunBits
    where size = c2num (undefined :: w)

  subA = arr (unNatSyncFunBits *** unNatSyncFunBits) >>> subNat size >>> arr NatSyncFunBits
    where size = c2num (undefined :: w)

  mulA = arr (unNatSyncFunBits *** unNatSyncFunBits) >>> mulNat size >>> arr NatSyncFunBits
    where size = c2num (undefined :: w)

  fromIntegerA n = toNatAC size n >>> arr NatSyncFunBits
    where size = c2num (undefined :: w)
