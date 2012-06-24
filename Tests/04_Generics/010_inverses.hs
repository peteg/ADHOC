-- check that some structure inverses really are.

module T where

import Tests.Basis
import Data.List ( genericLength )
import ADHOC.Generics

instance Structure Int Int where
  type SIwidth Int Int = One
  structure = sallocSM

instance StructureDest Int Int where
  destructure = (:[])

-- FIXME test sized lists, arithmetic, ... grep for other instances.

inst_dest_prop :: forall a. (Eq a, StructureDest Int a, Structure Int a) => a -> Bool
inst_dest_prop a =
    case runStateM structure (destructure a :: [Int]) of
      (a', []) -> a == a'

-- 'a' just gives us type information
-- the list has to be long enough
inst_dest_inst_prop :: forall a. (Eq a, StructureDest Int a, Structure Int a) => a -> [Int] -> Bool
inst_dest_inst_prop a xs = (genericLength xs >= i_width) -->
       (case ( runStateM structure xs :: (a, [Int])
             , runStateM structure (destructure (fst (runStateM structure xs) :: a)) :: (a, [Int])) of
         ((a', _), (a'', [])) -> a' == a'')
  where i_width = c2num (undefined :: SIwidth Int a)

-- 'a' just gives us type information
-- the list has to be long enough
-- inst/dest compose
dest_inst_prop :: forall a. (Eq a, StructureDest Int a, Structure Int a) => a -> [Int] -> Bool
dest_inst_prop a xs = (genericLength xs >= i_width) -->
       (case runStateM structure xs :: (a, [Int]) of
         (a, xs') -> (destructure a ++ xs' == xs && destructure a == (destructure a :: [Int])))
  where i_width = c2num (undefined :: SIwidth Int a)

prop_unit_id = property (\(a :: ()) -> inst_dest_prop a)
prop_unit_di = property (\xs -> dest_inst_prop (undefined :: ()) xs)
prop_unit_idi = property (\xs -> inst_dest_inst_prop (undefined :: ()) xs)

prop_pair_id = property (\(a :: (Int, Int)) -> inst_dest_prop a)
prop_pair_di = property (\xs -> dest_inst_prop (undefined :: (Int, Int)) xs)
prop_pair_idi = property (\xs -> inst_dest_inst_prop (undefined :: (Int, Int)) xs)

prop_triple_id = property (\(a :: (Int, Int, Int)) -> inst_dest_prop a)
prop_triple_di = property (\xs -> dest_inst_prop (undefined :: (Int, Int, Int)) xs)
prop_triple_idi = property (\xs -> inst_dest_inst_prop (undefined :: (Int, Int, Int)) xs)

prop_quadruple_id = property (\(a :: (Int, Int, Int, Int)) -> inst_dest_prop a)
prop_quadruple_di = property (\xs -> dest_inst_prop (undefined :: (Int, Int, Int, Int)) xs)
prop_quadruple_idi = property (\xs -> inst_dest_inst_prop (undefined :: (Int, Int, Int, Int)) xs)

prop_SizedList_id = property (\(a :: SizedList Eight Int) -> inst_dest_prop a)
prop_SizedList_di = property (\(xs, ys) -> dest_inst_prop (xs :: SizedList Eight Int) ys)
prop_SizedList_idi = property (\(xs, ys) -> inst_dest_inst_prop (xs :: SizedList Eight Int) ys)
