{-# LANGUAGE TypeFamilies #-}
{- Arrow-based types and classes for synchronous circuits.
 - Copyright   :  (C)opyright 2004-2005, 2009-2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -}
module ADHOC.Circuits
    ( module ADHOC.Basis
    , ArrowComb(..)
    , ArrowMux(..)
    , muxAC
    , muxA'

      -- * Command combinators and Unicode syntax for them.
    , notAC, andAC, iffAC, impAC, orAC, xorAC
    , (∧), (¬)
    , (↑), (∨), (⟺), (⟹), (⟸)

    , ArrowDelay(..), delayAC
    , ArrowInit(..)
    , ArrowCombLoop(..)

      -- * Extra generic circuits.
    , idB
    , fby
    , latchA
    ) where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude hiding ( id, (.) )
import ADHOC.Basis

-------------------------------------------------------------------
-- Synchronous circuit simulation arrows.
-------------------------------------------------------------------

-- FIXME all instances of 'ArrowComb' are transformers. We FIXME FIXME
-- run into problems with the ST monad if we expect B to map (~> :: *
-- -> * -> *) to the Boolean type for arrow. Try the transformer
-- type. Less general.
-- type family B ((~>) :: ((* -> * -> *) -> * -> *)) :: *

-- FIXME this implies that we cannot lift a ArrowComb instance up -
-- imagine the E arrow.

-- | Standard combinational logic. Minimal definition is 'falseA',
-- 'trueA', 'andA' and 'notA'. For the user's convenience, the arrow
-- type determines how booleans are represented.
-- FIXME making these command combinators enables constant propogation ??
class Arrow (~>) => ArrowComb (~>) where
  type B (~>) :: * -- FIXME not ST-friendly

  falseA :: env ~> B (~>)
  trueA :: env ~> B (~>)

  andA :: (B (~>), B (~>)) ~> B (~>)
  notA :: B (~>) ~> B (~>)

  nandA :: (B (~>), B (~>)) ~> B (~>)
  nandA = andA >>> notA

  orA :: (B (~>), B (~>)) ~> B (~>)
  orA = (notA *** notA) >>> andA >>> notA

  xorA :: (B (~>), B (~>)) ~> B (~>)
  xorA = (orA &&& (andA >>> notA)) >>> andA

  iffA :: (B (~>), B (~>)) ~> B (~>)
  iffA = xorA >>> notA

  impA :: (B (~>), B (~>)) ~> B (~>)
  impA = notA *** id >>> orA

  -- | Attach a note to a sub-circuit.
  note :: String -> (b ~> c) -> (b ~> c)
  note _ = id

-- | Binary 'ArrowComb' command combinators.
andAC, nandAC, orAC, xorAC, iffAC, impAC :: ArrowComb (~>) => (env ~> B (~>)) -> (env ~> B (~>)) -> (env ~> B (~>))
andAC = liftAC2 andA
nandAC = liftAC2 nandA
iffAC = liftAC2 iffA
impAC = liftAC2 impA
orAC = liftAC2 orA
xorAC = liftAC2 xorA
{-# INLINE andAC #-}
{-# INLINE nandAC #-}
{-# INLINE orAC #-}
{-# INLINE xorAC #-}
{-# INLINE iffAC #-}
{-# INLINE impAC #-}

notAC :: ArrowComb (~>) => (env ~> B (~>)) -> (env ~> B (~>))
notAC = liftAC notA
{-# INLINE notAC #-}

-- FIXME This is what we want, but command combinators break in GHC with infixr
-- infixr 8 ⟹, `impAC`, `xorAC`
-- infixl 8 ⟸
-- infixr 7 ∧, `andAC`
-- infixr 6 ∨, `orAC`
-- infixr 5 ⟺, `iffAC`

infixr 8 ⟹, `impAC`, `xorAC`
infixl 8 ⟸
infixl 7 ∧, `andAC` -- should be infixr
infixl 6 ∨, `orAC` -- should be infixr
infixl 5 ⟺, `iffAC` -- should be infixr

(¬) :: ArrowComb (~>) => (env ~> B (~>)) -> (env ~> B (~>))
(∧), (↑), (∨), (⟺), (⟹), (⟸) :: ArrowComb (~>) => (env ~> B (~>)) -> (env ~> B (~>)) -> (env ~> B (~>))
(∧) = andAC
(¬) = notAC
(↑) = nandAC -- Sheffer stroke
(∨) = orAC
(⟺) = iffAC
(⟹) = impAC
f ⟸ g = g ⟹ f

-- | A multiplexer, if-then-else in "Boolean" but switching an arbitary type.
-- Convention: if the bit is true, then we take the first otherwise the second.
class ArrowComb (~>) => ArrowMux (~>) v where
  muxA :: (B (~>), (v, v)) ~> v

-- | Trivial variant of 'muxA' that combines better with lifting.
muxA' :: ArrowMux (~>) v => (B (~>), v, v) ~> v
muxA' = arr (\(c, v0, v1) -> (c, (v0, v1))) >>> muxA

-- | Command-combinator variant of 'muxAC'.
muxAC :: ArrowMux (~>) v => (env ~> B (~>)) -> (env ~> v) -> (env ~> v) -> (env ~> v)
muxAC barr v0arr v1arr = proc env ->
  do b <- barr -< env
     v0 <- v0arr -< env
     v1 <- v1arr -< env
     muxA -< (b, (v0, v1))

-- | An initialised-delay operator, ala Lustre's @(->)@ (followed-by)
-- operator. Well-initialisation is verified by constructivity.
class Arrow (~>) => ArrowDelay (~>) v where
  delayA :: (v, v) ~> v

delayAC :: ArrowDelay (~>) v
        => (env ~> v) -- ^ Initial
        -> (env ~> v) -- ^ Recurring (delayed by one timestep)
        -> (env ~> v)
delayAC = liftAC2 delayA

-- | Statically-cyclic dynamically-acyclic combinational loops.
--
-- Intuitively we could support combinational cycles at all types, but
-- in practice we only use them at the boolean type.
class Arrow (~>) => ArrowCombLoop (~>) r where
  combLoop :: ((b, r) ~> (c, r)) -> (b ~> c)

-- | A \'boot\' bit, indicating the circuit is in an initial state.
class Arrow (~>) => ArrowInit (~>) where
  isInitialState :: env ~> B (~>)

----------------------------------------
-- FIXME Useful other things
----------------------------------------

-- | Acts as the identity on the 'B' type.
idB :: Arrow (~>) => B (~>) ~> B (~>)
idB = id

-- | Lustre's followed-by operator.
fby :: (ArrowDelay (~>) (B (~>)), ArrowInit (~>), ArrowMux (~>) v)
    => (e ~> v) -> (e ~> v) -> (e ~> v)
f `fby` g = proc e ->
  (| muxAC (isInitialState -< ())
           (f -< e)
           (g -< e) |)

-- | Latch a value.
latchA :: (ArrowDelay (~>) v, ArrowLoop (~>))
       => (v ~> v)
latchA = proc v ->
  do rec v' <- (| delayAC (returnA -< v) (returnA -< v') |)
     returnA -< v'
