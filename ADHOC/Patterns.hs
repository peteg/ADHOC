{- Circuit patterns transliterated from Lava / the Haskell Prelude / ...
 - Copyright   :  (C)opyright 2006, 2009-2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -
 - We count from /1/ to /n/, i.e. the first element of the list has index 1.
 - FIXME try to remove all the ~'s.
 -}
module ADHOC.Patterns
    ( mapA
    , mapAn
    , mapAC
    , mapACn
    , rowA
    , rowAn
    , zipWithA
    , zipWith3A
    , foldrA
    , foldr1A
    , foldr2A
    , foldrAC
    , conjoinA
    , disjoinA
    ) where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude ()

import ADHOC.Circuits

-------------------------------------------------------------------
-- Some extra Arrow combinators.
-- All are statically parameterised by the length of the list.
-------------------------------------------------------------------

-- | Similar to 'mapAC', where the constituents are a function of
-- their list index.
--
-- FIXME I don't think can be used as a command combinator due to the
-- @Integer@ argument.
mapACn :: Arrow (~>) => Integer -> (Integer -> ((env, b) ~> c)) -> ((env, [b]) ~> [c])
mapACn n farr = go 1
  where
    go i | i == succ n = proc (_env, []) -> returnA -< []
         | otherwise = proc (env, b : bs) ->
             (| (liftA2 (:)) (farr i -< (env, b)) (go (succ i) -< (env, bs)) |)

-- | FIXME describe
mapAC :: Arrow (~>) => Integer -> ((env, b) ~> c) -> ((env, [b]) ~> [c])
mapAC n farr = mapACn n (const farr)

-- | Similar to 'mapA', where the constituents are a function of their
-- list index.
mapAn :: Arrow (~>) => Integer -> (Integer -> (b ~> c)) -> ([b] ~> [c])
mapAn n farr = arr (\bs -> ((), bs)) >>> mapACn n (\i -> arr snd >>> farr i)

mapA :: Arrow (~>) => Integer -> (b ~> c) -> ([b] ~> [c])
mapA n farr = mapAn n (const farr)

-- | A variant version of "mapAccumL" I found useful. The constituents
-- are a function of their list index.
-- This is Lava's row, slightly mangled.
-- It does not enforce that the input list has length /n/.
rowAn :: Arrow (~>)
      => Integer
      -> (Integer -> (a, b) ~> (a, c))
      -> (a, [b]) ~> (a, [c])
rowAn n farr = go 1
  where
    go i | i == succ n = second (arr (const []))
         | otherwise = proc (a, ~(b : bs)) ->
             do (a',  c)  <- farr i -< (a, b)
                (a'', cs) <- go (succ i) -< (a', bs)
                returnA -< (a'', c : cs)

-- | A version of "mapAccumL" I found useful.
-- This is Lava's row, slightly mangled.
rowA :: Arrow (~>)
     => Integer
     -> (a, b) ~> (a, c)
     -> (a, [b]) ~> (a, [c])
rowA n farr = rowAn n (const farr)

-- | Zip an arrow over a pair of lists.
zipWithA :: Arrow (~>) => Integer -> ((b, c) ~> d) -> (([b], [c]) ~> [d])
zipWithA n0 f = go n0
  where
    go n = case n of
      0 -> arr (\([], []) -> [])
      _ -> arr (\ (s:ss, s':ss') -> ((s, s'), (ss, ss')))
             >>> (f *** go (pred n))
               >>> arr2 (:)

-- | Zip an arrow over a triple of lists.
zipWith3A :: Arrow (~>) => Integer -> ((b, c, d) ~> e) -> (([b], [c], [d]) ~> [e])
zipWith3A 0 _f = arr (\([], [], []) -> [])
zipWith3A n  f =
    arr (\ ~(s:ss, s':ss', s'':ss'') -> ((s, s', s''), (ss, ss', ss'')))
      >>> (f *** zipWith3A (pred n) f)
        >>> arr2 (:)

-- | Right fold.
foldrA :: Arrow (~>)
       => Integer
       -> (b, c) ~> b
       -> () ~> b
       -> [c] ~> b
foldrA 0 _f z = proc [] -> z -< ()
foldrA n  f z = proc (c : cs) ->
  do b <- foldrA (pred n) f z -< cs
     f -< (b, c)

-- | Right fold, no base case.
foldr1A :: Arrow (~>)
       => Integer
       -> (b, b) ~> b
       -> [b] ~> b
foldr1A 0 _f = error "foldr1A not defined for empty lists"
foldr1A 1 _f = arr (\[x] -> x)
foldr1A n f = proc (c : cs) ->
  do b <- foldr1A (pred n) f -< cs
     f -< (b, c)

-- | Right fold over a pair of lists.
-- FIXME as fusion doesn't work, we hand fuse in zip.
foldr2A :: Arrow (~>)
       => Integer
       -> (b, (c, d)) ~> b
       -> () ~> b
       -> ([c], [d]) ~> b
foldr2A 0 _f z = proc ([], []) -> z -< ()
foldr2A n  f z = proc ~(c : cs, d : ds) ->
  do b <- foldr2A (pred n) f z -< (cs, ds)
     f -< (b, (c, d))

-- | FIXME
foldrAC :: Arrow (~>)
       => Integer
       -> (env, (b, c)) ~> b
       -> env ~> b
       -> (env, [c]) ~> b
foldrAC 0 _f z = proc (env, []) -> z -< env
foldrAC n  f z = proc ~(env, c : cs) ->
  do b <- foldrAC (pred n) f z -< (env, cs)
     f -< (env, (b, c))

conjoinA :: ArrowComb (~>) => Integer -> ([B (~>)] ~> B (~>))
conjoinA n = foldrA n andA trueA

disjoinA :: ArrowComb (~>) => Integer -> ([B (~>)] ~> B (~>))
disjoinA n = foldrA n orA falseA
