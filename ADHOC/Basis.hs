{-# LANGUAGE Arrows, BangPatterns, FlexibleContexts, NoMonomorphismRestriction, RankNTypes, TypeFamilies, TypeOperators #-}
{- Project-wide types and external dependencies.
 - Copyright   :  (C)opyright 2004-2005, 2009-2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -}
module ADHOC.Basis
    ( module Prelude
    , module Control.Arrow
    , module Control.Arrow.Transformer
    , module Control.Category
    , module Data.Boolean

    , module Debug.Trace

    , assert

    , untilM

    , ArchView, BitView

    , AgentID, ProbeID
    , Probe(..)
    , Zero(..)

    , BDD, reorder, dynamicReordering, bddPrintInfo -- FIXME

    , arr2
    , dupA
    , liftA2
    , liftAC
    , liftAC2
    , swapA
    , unitA
    , assocA, unassocA

    , combinations

      -- * State applicative functor/monad.
    , StateM(..)
    , getSM
    , modifySM
    , nextUniqueSM
    , sallocSM
    , recSM

    , Id(..)

    , prime
    , tmp_name
    , on
    , foldObsM
    , mapObsM
    ) where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude hiding ( id, (.), mapM, sequence )

import Control.Applicative ( Applicative(..) )
import Control.Arrow hiding ( (<+>) )
import Control.Arrow.Transformer ( ArrowTransformer(..) )
import Control.Category	( Category(..) )
import Control.Exception ( assert )

import Data.Boolean
import Data.Boolean.CUDD as BDD

import Debug.Trace

bddPrintInfo :: IO ()
bddPrintInfo = BDD.printInfo

-------------------------------------------------------------------
-- Views of a circuit.
-------------------------------------------------------------------

-- | An architecture-level view.
data ArchView

-- | A bit-level view.
data BitView

-------------------------------------------------------------------
-- Propositional logic: types and syntactic overloading.
-------------------------------------------------------------------

type AgentID = String

type ProbeID = String

-- | Overload the syntax for the proposition "the probe reads @true@".
class Probe f where
  probe :: ProbeID -> f

-------------------------------------------------------------------
-- FIXME
-------------------------------------------------------------------

-- | Monadic fixpoint combinator: iterate until the predicate returns
-- @True@.
untilM :: Monad m => (a -> m Bool) -> (a -> m a) -> a -> m a
untilM p f = go
  where
    go a =
      do pa <- p a
         if pa then return a else (f a >>= go)

-- | 'zeroA' designates some fixed value of @v@, for squashing
-- observations.
class Arrow (~>) => Zero (~>) v where
  zeroA :: env ~> v

instance Arrow (~>) => Zero (~>) () where
  zeroA = arr (const ())

instance (Zero (~>) a, Zero (~>) b) => Zero (~>) (a, b) where
  zeroA = zeroA &&& zeroA

-------------------------------------------------------------------
-- Some extra Arrow combinators.
-------------------------------------------------------------------

-- | Lift a binary function into an arrow.
arr2 :: Arrow (~>) => (a -> b -> c) -> ((a, b) ~> c)
arr2 = arr . uncurry
{-# INLINE arr2 #-}

-- | Fanout.
dupA :: Arrow (~>) => b ~> (b, b)
dupA = arr (\x -> (x,x))
{-# INLINE dupA #-}

-- | Lift a unary 'Arrow' into a command combinator.
liftAC :: Arrow (~>) => (b ~> c) -> (env ~> b) -> (env ~> c)
liftAC op f = f >>> op
{-# INLINE liftAC #-}

-- | Lift a binary 'Arrow' into a command combinator.
liftAC2 :: Arrow (~>) => ((b, c) ~> d) -> (env ~> b) -> (env ~> c) -> (env ~> d)
liftAC2 op f g = f &&& g >>> op
{-# INLINE liftAC2 #-}

-- | Lift a binary function into an 'Arrow' command combinator.
liftA2 :: Arrow (~>) => (b -> c -> d) -> (env ~> b) -> (env ~> c) -> (env ~> d)
liftA2 = liftAC2 . arr2
{-# INLINE liftA2 #-}

-- | Swap the elements of a tuple.
swapA :: Arrow (~>) => (a, b) ~> (b, a)
swapA = arr (\(a, b) -> (b, a))
{-# INLINE swapA #-}

-- | The identity 'Arrow' on tuples: useful for monomorphising
-- 'Arrow's.
unitA :: Arrow (~>) => () ~> ()
unitA = id
{-# INLINE unitA #-}

assocA :: Arrow (~>) => ((a, b), c) ~> (a, (b, c))
assocA = arr $ \((a, b), c) -> (a, (b, c))

unassocA :: Arrow (~>) => (a, (b, c)) ~> ((a, b), c)
unassocA = arr $ \(a, (b, c)) -> ((a, b), c)

-------------------------------------------------------------------
-- Combinations.
-------------------------------------------------------------------

-- | /n-choose-k/: Generate all sublists of length k from a list of length n.
combinations :: Integer -- ^ /n/
             -> Integer -- ^ /k/
             -> [a] -> [[a]]
combinations _ _ [] = []        -- Don't include empty combinations
combinations n k as@(ah:at)
    | k <= 0 = [[]]
    | k > n = []
    | k == n = [as]
    | otherwise = (map (ah:) $ combinations (pred n) (pred k) at)
                    ++ combinations (pred n) k at

-------------------------------------------------------------------
-- @Id@ is defined in "Data.Traversable" but not exported.
-------------------------------------------------------------------

newtype Id a = Id { getId :: a }

instance Functor Id where
        fmap f (Id x) = Id (f x)

instance Applicative Id where
        pure = Id
        Id f <*> Id x = Id (f x)

-------------------------------------------------------------------
-- Cheap and cheerful State applicative functor/monad.
-------------------------------------------------------------------

-- | State applicative functor/monad.
newtype StateM s a = StateM { runStateM :: s -> (a, s) }

instance Functor (StateM s) where
    fmap f (StateM g) = StateM (g >>> first f)

instance Applicative (StateM s) where
    pure x = StateM (\s -> (x, s))
    StateM f <*> StateM x = StateM (f >>> second x >>> (\(fv, (xv, s)) -> (fv xv, s)))

instance Monad (StateM s) where
    return = pure
    StateM f >>= g = StateM (f >>> (\(a, s') -> runStateM (g a) s'))

getSM :: StateM s s
getSM = StateM dupA

modifySM :: (s -> (a, s)) -> StateM s a
modifySM = StateM

nextUniqueSM :: Enum n => StateM n n
nextUniqueSM = StateM (\s -> (s, succ s))

sallocSM :: StateM [s] s
sallocSM = StateM (\(x:xs) -> (x, xs))

-- | mfix
recSM :: (a -> StateM s a) -> StateM s a
recSM f = StateM (\s -> let ~(a, s') = runStateM (f a) s in (a, s'))

-------------------------------------------------------------------
-- Miscellaneous functions.
-------------------------------------------------------------------

-- | Do the "next state" thing.
prime :: String -> String
prime s = s ++ "'"

-- | \"Temporary\" variable name.
tmp_name :: String -> String
tmp_name s = "@tmp_" ++ s

-- | NAD's all-purpose binary projection operator.
--
-- Example: @sortBy (compare `on` snd)@
on :: (t1 -> t1 -> t) -> (t2 -> t1) -> t2 -> t2 -> t
op `on` f = \x y -> f x `op` f y

-- | Determine the possible observations for a set of states @ss@ with
-- respect to the bits @obsBits@ and fold a function across them.
-- FIXME abstract out the cube building operations
foldObsM :: (Boolean b, Eq b, Monad m)
         => b -> [b] -> (a -> (b, b) -> m a) -> a -> m a
foldObsM ss obsBits fun a0 = mkObs ss true obsBits fun return a0
  where
    mkObs sso obs obits s f a
      | sso == false = f a
      | otherwise =
        case obits of
          [] -> s a (sso, obs) >>= f
          o : os ->
            -- FIXME hope this kills sso before we backtrack.
            -- mkObs (sso /\ neg o) (obs /\ neg o) os s (mkObs (sso /\ o) (obs /\ o) os s f) a
            mkObs (sso /\ neg o) (obs /\ neg o) os s (mkObs (ss /\ obs /\ o) (obs /\ o) os s f) a

-- | Determine the possible observations for a set of states @ss@ with
-- respect to the bits @obsBits@ and map a function across them.
mapObsM :: forall b m.
           (Boolean b, Eq b, Monad m)
        => b -> [b] -> ((b, b) -> m ()) -> m ()
mapObsM ss obsBits fun = mkObs ss true obsBits fun (return ())
  where
    mkObs :: b -> b -> [b] -> ((b, b) -> m ()) -> m () -> m ()
    mkObs !sso !obs obits s f
      | sso == false = f
      | otherwise =
        case obits of
          [] -> s (sso, obs) >> f
          o : os ->
            -- FIXME hope this kills sso before we backtrack.
            -- mkObs (sso /\ neg o) (obs /\ neg o) os s (mkObs (sso /\ o) (obs /\ o) os s f)
            mkObs (sso /\ neg o) (obs /\ neg o) os s (mkObs (ss /\ obs /\ o) (obs /\ o) os s f)
