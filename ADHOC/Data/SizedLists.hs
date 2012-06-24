{-# LANGUAGE TypeFamilies #-}
{- Cheap and cheesy lists with sizes in their types.
 - Copyright   :  (C)opyright 2006, 2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -
 - We count from /1/ to /n/, i.e. the first element of the list has index 1.
 -}
module ADHOC.Data.SizedLists where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude hiding ( id, (.) )
import Control.Monad ( liftM )
import Test.QuickCheck	( Arbitrary(..), vectorOf )

import ADHOC.Circuits
import ADHOC.Generics
import ADHOC.Patterns

-------------------------------------------------------------------
-- Lists with a static sized type.
-------------------------------------------------------------------

newtype SizedList size a = SizedList { unSizedList :: [a] }
    deriving (Eq, Show)

instance (Card size, Arbitrary a) => Arbitrary (SizedList size a) where
    arbitrary = fmap SizedList (vectorOf width arbitrary)
      where width = c2num (undefined :: size) :: Int

idSL :: (Card size, Category (~>)) => size -> SizedList size a ~> SizedList size a
idSL = const id

-- | Similar to 'asTypeOf', but just for 'SizedList' lengths.
asLengthOf :: SizedList size a -> SizedList size b -> SizedList size a
asLengthOf = const

-- | Similar to 'asLengthOf', but uses just a size.
withLength :: SizedList size a -> size -> SizedList size a
withLength = const

-- | An arrowized version of the constructor, unsafe, not exported to the end user.
sizedListA :: Arrow arrow => arrow [a] (SizedList size a)
sizedListA = arr SizedList

unSizedListA :: Arrow arrow => arrow (SizedList size a) [a]
unSizedListA = arr unSizedList

instance (Card size, Zero (~>) a) => Zero (~>) (SizedList size a) where
  zeroA = zeroA >>> replicateSL

instance (Card size, StructureDest s a) => StructureDest s (SizedList size a) where
  destructure = concat .  map destructure . unSizedList

instance (Card size, Structure s a) => Structure s (SizedList size a) where
  type SIwidth s (SizedList size a) = CardMul size (SIwidth s a)
  structure = SizedList <$> for [1..width] (const structure)
    where
      width = c2num (undefined :: size) :: Integer

-------------------------------------------------------------------
-- Constructor: replicateL.
-------------------------------------------------------------------

-- | FIXME: grotty, run-time errors
mkSizedListA :: forall (~>) size a. (Arrow (~>), Card size) => [a] ~> SizedList size a
mkSizedListA = proc xs ->
  do let
       width = c2num (undefined :: size) :: Int
       l = length xs
     returnA -< if l /= width
                  then error $ "mkSizedList: list has length " ++ show l ++ " /= size " ++ show width
                  else SizedList xs

-- | Fan out a value.
replicateSL :: forall (~>) size a. (Arrow (~>), Card size)
            => a ~> SizedList size a
replicateSL = arr (SizedList . replicate (c2num (undefined :: size)))

-- | Make a 'SizedList' using a function. The 'size' measures the list
-- length, i.e. list element indices start at 1.
mkSizedListf :: forall size a. (Card size)
             => (Integer -> a) -> SizedList size a
mkSizedListf f = SizedList [ f i | i <- [1 .. c2num (undefined :: size) :: Integer] ]

-- | Make a 'SizedList' using a function, arrow command combinator
-- edition. The 'size' measures the list length., i.e. list element
-- indices start at 1.
mkSizedListAC :: forall (~>) size env a. (Arrow (~>), Card size)
              => (Integer -> env ~> a) -> env ~> SizedList size a
mkSizedListAC f = mkL 1 >>> sizedListA
    where
      width = c2num (undefined :: size)

      mkL :: Integer -> env ~> [a]
      mkL i | i == succ width = arr (const [])
            | otherwise = proc env ->
                do a  <- f i -< env
                   as <- mkL (succ i) -< env
                   returnA -< a : as

-- | Make a 'SizedList' using a function. The 'size' measures the list
-- length, i.e. list element indices start at 1. We also thread a
-- value through the constructor ala 'rowSLn'.
fanoutSL :: forall (~>) size a b env. (Arrow (~>), Card size)
               => (Integer -> (env, a) ~> (a, b)) -> (env, a) ~> (a, SizedList size b)
fanoutSL f = mkL 1 >>> second sizedListA
    where
      width = c2num (undefined :: size)

      mkL :: Integer -> (env, a) ~> (a, [b])
      mkL i | i == succ width = arr (\(_env, a) -> (a, []))
            | otherwise = proc (env, a) ->
                do (a', b) <- f i -< (env, a)
                   (a'', bs) <- mkL (succ i) -< (env, a')
                   returnA -< (a'', b : bs)

mkSizedListSingletonA :: forall (~>) a. Arrow (~>)
                      => a ~> SizedList One a
mkSizedListSingletonA = arr (SizedList . (:[]))

-------------------------------------------------------------------
-- Operations.
-------------------------------------------------------------------

foldrSL :: forall arrow size b c. (Arrow arrow, Card size)
        => arrow (b, c) b
        -> arrow () b
        -> arrow (SizedList size c) b
foldrSL f z = unSizedListA >>> foldrA (c2num (undefined :: size)) f z

foldr1SL :: forall (~>) size b. (Arrow (~>), Card size)
         => (b, b) ~> b
         -> SizedList size b ~> b
foldr1SL f = unSizedListA >>> foldr1A (c2num (undefined :: size)) f

mapSL :: forall (~>) size b c. (Arrow (~>), Card size)
      => b ~> c
      -> SizedList size b ~> SizedList size c
mapSL f = unSizedListA >>> mapA (c2num (undefined :: size)) f >>> sizedListA

mapSLn :: forall (~>) size b c. (Arrow (~>), Card size)
       => (Integer -> b ~> c) -> SizedList size b ~> SizedList size c
mapSLn f = unSizedListA >>> mapAn (c2num (undefined :: size)) f >>> sizedListA

mapSLC :: forall (~>) size b c env. (Arrow (~>), Card size)
      => (env, b) ~> c
      -> (env, SizedList size b) ~> SizedList size c
mapSLC f = id *** unSizedListA >>> mapAC (c2num (undefined :: size)) f >>> sizedListA

-- | FIXME a semi-static?? map.
mapSLs :: forall (~>) size b c env. (Arrow (~>), Card size)
       => (b -> (env ~> c))
       -> SizedList size b
       -> env ~> SizedList size c
mapSLs f sl = foldr f' z (unSizedListA sl) >>> sizedListA
  where
    f' b rarr = liftA2 (:) (f b) rarr
    z = arr (const [])

rowSLn :: forall arrow size a b c .
          (Arrow arrow, Card size)
       => (Integer -> arrow (a, b) (a, c))
       -> arrow (a, SizedList size b) (a, SizedList size c)
rowSLn f =
         second unSizedListA
     >>> rowAn (c2num (undefined :: size)) f
     >>> second sizedListA

rotateSL :: forall (~>) size b. (Arrow (~>), Card size)
         => SizedList size b ~> SizedList size b
rotateSL = unSizedListA >>> arr rotate >>> sizedListA
  where
    rotate [] = []
    rotate (x:xs) = xs ++ [x]

sequenceSL :: forall (~>) size b m. (Arrow (~>), Card size, Monad m)
           => SizedList size (m b) ~> m (SizedList size b)
sequenceSL = unSizedListA >>> arr (liftM sizedListA . sequence)

zipWithSL :: forall (~>) b c d size . (Arrow (~>), Card size)
          => (b, c) ~> d
          -> (SizedList size b, SizedList size c) ~> (SizedList size d)
zipWithSL f = (unSizedListA *** unSizedListA) >>> zipWithA n f >>> sizedListA
    where n = c2num (undefined :: size)

-- | FIXME a semi-static?? 'zipWith'. This is some form of currying.
zipWithSLs :: forall (~>) size b c d. (Arrow (~>), Card size)
           => (b -> (c ~> d))
           -> SizedList size b
           -> (SizedList size c ~> SizedList size d)
zipWithSLs f sl = unSizedListA >>> foldr f' z (unSizedListA sl) >>> sizedListA
  where
    f' b rarr = proc (c:cs) ->
      do d  <- f b -< c
         ds <- rarr -< cs
         returnA -< d : ds
    z = arr (const [])

conjoinSL :: forall (~>) size. (Arrow (~>), ArrowComb (~>), Card size)
         => SizedList size (B (~>)) ~> B (~>)
conjoinSL = unSizedListA >>> conjoinA (c2num (undefined :: size))

disjoinSL :: forall (~>) size. (Arrow (~>), ArrowComb (~>), Card size)
         => SizedList size (B (~>)) ~> B (~>)
disjoinSL = unSizedListA >>> disjoinA (c2num (undefined :: size))
