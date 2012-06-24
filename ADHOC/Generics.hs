{-# LANGUAGE TypeFamilies #-}
{- Arrow-based types and classes for synchronous circuits.
 - Copyright   :  (C)opyright 2004-2005, 2009-2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)

The type-level naturals here are cheesy. The hope is to replace them
with GHC's built-in implementation when it is cooked.

-}
module ADHOC.Generics
    ( module Control.Applicative
    , module Data.Traversable
    , module Data.Monoid

      -- * Type-level numbers
    , D0(..), D1(..), D2(..), D3(..), D4(..), D5(..), D6(..)
    , D7(..), D8(..), D9(..), Sz(..)
    , Digits(..), Card(..)
    , CardAdd, CardMul
    , Naught
    , One
    , Two
    , Three
    , Four
    , Five
    , Six
    , Seven
    , Eight
    , Nine
    , Fourteen
    , Fifteen

      -- * Generic structures
    , StructureDest(..)
    , Structure(..)
    ) where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Control.Applicative hiding ( liftA2 )
import Control.Monad
import Data.Monoid
import Data.Traversable hiding ( sequence )

import Prelude hiding ( id, (.) )
import ADHOC.Basis

-------------------------------------------------------------------
-- Type-level numbers.
--
-- Following Oleg Kiselyov's "Number-parameterized types"
--   http://okmij.org/ftp/Haskell/number-parameterized-types.html
--
-- The hope is to replace this lock-stock when GHC's type-level nats
-- are mature enough.
--
-- http://hackage.haskell.org/trac/ghc/ticket/4385
--
-- For that reason it is not worth sweating this (here or in the
-- examples).
-------------------------------------------------------------------

data D0 a = D0 a
data D1 a = D1 a
data D2 a = D2 a
data D3 a = D3 a
data D4 a = D4 a
data D5 a = D5 a
data D6 a = D6 a
data D7 a = D7 a
data D8 a = D8 a
data D9 a = D9 a

class Digits ds where		-- class of digit sequences
    ds2num:: (Num a) => ds -> a -> a     -- CPS style

data Sz = Sz			-- zero size (or the Nil of the sequence)

instance Digits Sz where
    ds2num _ acc = acc

instance (Digits ds) => Digits (D0 ds) where
    ds2num dds acc = ds2num (t22 dds) (10*acc)
instance (Digits ds) => Digits (D1 ds) where
    ds2num dds acc = ds2num (t22 dds) (10*acc + 1)
instance (Digits ds) => Digits (D2 ds) where
    ds2num dds acc = ds2num (t22 dds) (10*acc + 2)
instance (Digits ds) => Digits (D3 ds) where
    ds2num dds acc = ds2num (t22 dds) (10*acc + 3)
instance (Digits ds) => Digits (D4 ds) where
    ds2num dds acc = ds2num (t22 dds) (10*acc + 4)
instance (Digits ds) => Digits (D5 ds) where
    ds2num dds acc = ds2num (t22 dds) (10*acc + 5)
instance (Digits ds) => Digits (D6 ds) where
    ds2num dds acc = ds2num (t22 dds) (10*acc + 6)
instance (Digits ds) => Digits (D7 ds) where
    ds2num dds acc = ds2num (t22 dds) (10*acc + 7)
instance (Digits ds) => Digits (D8 ds) where
    ds2num dds acc = ds2num (t22 dds) (10*acc + 8)
instance (Digits ds) => Digits (D9 ds) where
    ds2num dds acc = ds2num (t22 dds) (10*acc + 9)

t22 :: f x -> x
t22 = undefined

-- Class of non-negative numbers
-- This is a restriction on Digits. It is not possible to make
-- such a restriction in SML.
class {- (Digits c) => -} Card c where
    c2num:: (Num a) => c -> a

instance Card Sz where c2num c = ds2num c 0
--instance (NonZeroDigit d, Digits (d ds)) => Card (Sz (d ds)) where
instance (Digits ds) => Card (D0 ds) where c2num c = ds2num c 0 -- FIXME verify
instance (Digits ds) => Card (D1 ds) where c2num c = ds2num c 0
instance (Digits ds) => Card (D2 ds) where c2num c = ds2num c 0
instance (Digits ds) => Card (D3 ds) where c2num c = ds2num c 0
instance (Digits ds) => Card (D4 ds) where c2num c = ds2num c 0
instance (Digits ds) => Card (D5 ds) where c2num c = ds2num c 0
instance (Digits ds) => Card (D6 ds) where c2num c = ds2num c 0
instance (Digits ds) => Card (D7 ds) where c2num c = ds2num c 0
instance (Digits ds) => Card (D8 ds) where c2num c = ds2num c 0
instance (Digits ds) => Card (D9 ds) where c2num c = ds2num c 0

-- | Add two cardinalities.
data CardAdd c1 c2

instance (Card c1, Card c2) => Card (CardAdd c1 c2) where
  c2num _ = c2num (undefined :: c1) + c2num (undefined :: c2)

-- | Multiply two cardinalities.
data CardMul c1 c2

instance (Card c1, Card c2) => Card (CardMul c1 c2) where
  c2num _ = c2num (undefined :: c1) * c2num (undefined :: c2)

type Naught   = D0 Sz
type One      = D1 Sz
type Two      = D2 Sz
type Three    = D3 Sz
type Four     = D4 Sz
type Five     = D5 Sz
type Six      = D6 Sz
type Seven    = D7 Sz
type Eight    = D8 Sz
type Nine     = D9 Sz
type Fourteen = D1 (D4 Sz)
type Fifteen  = D1 (D5 Sz)

-------------------------------------------------------------------
-- Generic structures.
-------------------------------------------------------------------

-- | A class of \"structural\" types that can be generically
-- destructured. These types do not have to reflect their sizes in
-- their types (i.e. it supports recursive types).
--
-- FIXME Original motivation: we can make Kesterel an instance of the
-- K classes but we don't know how big the signal environment is.
class StructureDest s a where
  destructure :: a -> [s]

instance StructureDest s () where
  destructure = mempty

instance (StructureDest s a, StructureDest s b) => StructureDest s (a, b) where
    destructure = \(x, y) -> destructure x ++ destructure y

instance (StructureDest s a, StructureDest s b, StructureDest s c) => StructureDest s (a, b, c) where
    destructure = \(x, y, z) -> concat [destructure x, destructure y, destructure z]

instance (StructureDest s a, StructureDest s b, StructureDest s c, StructureDest s d)
       => StructureDest s (a, b, c, d) where
  destructure = \(a, b, c, d) -> concat [destructure a, destructure b, destructure c, destructure d]

instance (StructureDest s a, StructureDest s b, StructureDest s c, StructureDest s d, StructureDest s e)
       => StructureDest s (a, b, c, d, e) where
    destructure = \(a, b, c, d, e) -> concat [destructure a, destructure b, destructure c, destructure d, destructure e]

--------------------

-- | A class of types @a@ that is isomorphic to a (finite, particular
-- length) list of @s@s.
class (StructureDest s a, Card (SIwidth s a)) => Structure s a where
  type SIwidth s a :: *
  structure :: StateM [s] a

instance Structure s () where
  type SIwidth s () = Naught
  structure = return ()

instance (Structure s a, Structure s b)
       => Structure s (a, b) where
  type SIwidth s (a, b) = CardAdd (SIwidth s a) (SIwidth s b)
  structure = liftM2 (,) structure structure

instance (Structure s a, Structure s b, Structure s c)
       => Structure s (a, b, c) where
  type SIwidth s (a, b, c) = CardAdd (SIwidth s a) (CardAdd (SIwidth s b) (SIwidth s c))
  structure = liftM3 (,,) structure structure structure

instance (Structure s a, Structure s b, Structure s c, Structure s d)
       => Structure s (a, b, c, d) where
  type SIwidth s (a, b, c, d) = CardAdd (SIwidth s a) (CardAdd (SIwidth s b) (CardAdd (SIwidth s c) (SIwidth s d)))
  structure = liftM4 (,,,) structure structure structure structure

instance (Structure s a, Structure s b, Structure s c, Structure s d, Structure s e)
       => Structure s (a, b, c, d, e) where
  type SIwidth s (a, b, c, d, e) = CardAdd (SIwidth s a) (CardAdd (SIwidth s b) (CardAdd (SIwidth s c) (CardAdd (SIwidth s d) (SIwidth s e))))
  structure = liftM5 (,,,,) structure structure structure structure structure

--------------------

-- Orphan instance used in Arithmetic for SyncFun.
instance StructureDest (Maybe Integer) (Maybe Integer) where
  destructure = (:[])

instance Structure (Maybe Integer) (Maybe Integer) where
  type SIwidth (Maybe Integer) (Maybe Integer) = One
  structure = sallocSM
