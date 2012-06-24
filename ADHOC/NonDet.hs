{- Circuit-level non-determinism.
 - Copyright   :  (C)opyright 2006, 2009, 2010 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -
-- FIXME: the fairness here is a pretty loose idea.
-- It's enough for the robot example but there's clearly some problems
--   in the general case.
 -}
module ADHOC.NonDet
    ( ArrowNonDet(..)

    , nondetAC
    , nondetFairAC
    , nondetBitA
    , nondetFairBitA
    , nondetListA
    , nondetBitsA
    , nondetInstA

      -- * Non-deterministically initialised delays.
    , ArrowUnsafeNonDet(..)
    , nondetLatchAC
    , nondetChooseAC
    ) where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------
import Prelude hiding ( id, (.) )
import Data.List ( genericSplitAt )

import ADHOC.Circuits
import ADHOC.Generics

-------------------------------------------------------------------

-- | \"Demonic\" non-deterministic choice. Also called external
-- choice.
class Arrow (~>) => ArrowNonDet (~>) v where
  -- | Non-deterministic choice between two values.
  nondetA :: (v, v) ~> v
  -- | \"Fairly\" non-deterministically choose between two values.
  nondetFairA :: (v, v) ~> v

-- | Non-deterministic choice between two 'Arrow's
nondetAC :: ArrowNonDet (~>) v => (env ~> v) -> (env ~> v) -> (env ~> v)
nondetAC = liftAC2 nondetA

-- | \"Fair\" non-deterministic choice between two 'Arrow's.
nondetFairAC :: ArrowNonDet (~>) v => (env ~> v) -> (env ~> v) -> (env ~> v)
nondetFairAC = liftAC2 nondetFairA

-- | Unsafe primitives, useful for efficient definitions. The proof
-- obligation is that FIXME the predicate is true often enough.
--
--FIXME need fair variants?
class ArrowComb (~>) => ArrowUnsafeNonDet (~>) v where
  -- | Each instant choose an object of type @v@ that satisfies the
  -- predicate.
  unsafeNonDetInstAC :: ((env, v) ~> B (~>)) -> env ~> v

  -- | Non-deterministically choose an object of type @v@ that
  -- satisfies the predicate in the initial instant. Generate a new
  -- value in the (recurring) next instant if the second arrow yields
  -- true, otherwise use the value from the current instant.
  unsafeNonDetAC :: ((env, v) ~> B (~>)) -- ^ predicate
                 -> (env ~> B (~>)) -- ^ resample?
                 -> (env ~> v)

-- | Non-deterministically choose an object of type @v@ and hold it
-- constant for all time.
--
-- FIXME unsafe
nondetLatchAC :: (ArrowLoop (~>), ArrowUnsafeNonDet (~>) v)
              => ((env, v) ~> B (~>)) -> (env ~> v)
nondetLatchAC predA = proc env ->
  do rec x <- (| unsafeNonDetAC (\v -> predA -< (env, v)) (falseA -< x) |)
     returnA -< x

-- | Non-deterministically choose an object of type @v@ at every
-- instant.
nondetChooseAC :: (ArrowLoop (~>), ArrowUnsafeNonDet (~>) v)
               => ((env, v) ~> B (~>)) -> (env ~> v)
nondetChooseAC predA = proc env ->
  do rec x <- (| unsafeNonDetAC (\v -> predA -< (env, v)) (trueA -< x) |)
     returnA -< x

-- | Non-deterministic choice of a bit every instant.
nondetBitA :: (ArrowComb (~>), ArrowNonDet (~>) (B (~>)))
           => env ~> B (~>)
nondetBitA = trueA `nondetAC` falseA

-- | Fair non-deterministic choice of a bit every instant.
nondetFairBitA :: (ArrowComb (~>), ArrowNonDet (~>) (B (~>)))
               => env ~> B (~>)
nondetFairBitA = trueA `nondetFairAC` falseA

-- | Non-deterministically choose an element of the list.  Note this
-- would not be statistically robust if /n/ is not a power of two, but
-- for pure non-determinism this is not observable.
nondetListA :: (ArrowComb (~>), ArrowMux (~>) v, ArrowNonDet (~>) (B (~>)))
            => Integer -> ([v] ~> v)
nondetListA n0 | n0 > 0 =
  proc vs ->
    do bits <- nondetBitsA len -< ()
       mkA n0 -< (vs, bits)
  where
    len :: Integer
    len = ceiling $ (logBase 2 (fromInteger n0) :: Double)

    mkA 1 = proc ([v], _) -> returnA -< v
    mkA 2 = proc ([l, r], b:_) -> muxA -< (b, (l, r))
    mkA n = proc (vs, b:bs) ->
              do let (ls, rs) = genericSplitAt size_l vs
                 l <- mkA size_l -< (ls, bs)
                 r <- mkA (n - size_l) -< (rs, bs)
                 muxA -< (b, (l, r))
      where size_l = n `div` 2
nondetListA n = error $ "nondetListA: width '" ++ show n ++ "' is not >= 0"

-- | non-deterministically choose /n/ bits.
nondetBitsA :: (ArrowComb (~>), ArrowNonDet (~>) (B (~>)), Eq n, Num n)
           => n -> env ~> [B (~>)]
nondetBitsA 0 = arr (const [])
nondetBitsA b = liftA2 (:) nondetBitA (nondetBitsA (b - 1))

-- | Non-deterministically instantiate an object of type
-- @a@. Generates a new object every instant.
nondetInstA :: forall (~>) a.
               (ArrowComb (~>), ArrowNonDet (~>) (B (~>)), Structure (B (~>)) a)
            => () ~> a
nondetInstA = nondetBitsA width >>> arr (fst . runStateM structure)
  where
    width :: Integer
    width = c2num (undefined :: SIwidth (B (~>)) a)
