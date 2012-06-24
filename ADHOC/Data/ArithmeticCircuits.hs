{- Arithmetic circuits.
 - Copyright   :  (C)opyright 2006, 2009-2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -
 - These circuits aren't great circuits, but we're really
   only interested in the boolean functions anyway.
 - MSB first.
 - Parameterised by term-level Integers.
 - FIXME think harder about the twiddles. A lot are useless.
 - FIXME append 'A' to all of these.
 -}
module ADHOC.Data.ArithmeticCircuits where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude hiding ( id, (.) )
import Data.List ( genericDrop, genericReplicate )

import ADHOC.Circuits
import ADHOC.Patterns

-------------------------------------------------------------------
-- General arithmetic circuits.
-------------------------------------------------------------------

-- | Equality of two bit patterns.
equalA :: ArrowComb (~>) => Integer -> (([B (~>)], [B (~>)]) ~> B (~>))
-- FIXME this does not fuse (unsurprisingly).
-- equal n = zipWithA n iffA >>> conjoinA n
equalA n = foldr2A n (second iffA >>> andA) trueA

-- | Full adder: given a carry-in and two bits, yield their sum and a
-- carry out.
fullAdd :: ArrowComb (~>) => (B (~>), (B (~>), B (~>))) ~> (B (~>), B (~>))
fullAdd = proc (carryIn, ab) ->
    do (sum1, carry1) <- halfAdd -< ab
       (sum0, carry2) <- halfAdd -< (carryIn, sum1)
       carryOut       <- xorA    -< (carry1, carry2)
       returnA -< (sum0, carryOut)
  where
    halfAdd :: ArrowComb (~>) => (B (~>), B (~>)) ~> (B (~>), B (~>))
    halfAdd = xorA &&& andA

-- | Simple ripple-carry adder.
adder :: ArrowComb (~>) => Integer -> (B (~>), ([B (~>)], [B (~>)])) ~> (B (~>), [B (~>)])
adder n0 =
  case n0 of
    0 -> proc (cin, ([], [])) -> returnA -< (cin, [])
    n -> proc (cin, (x:xs, y:ys)) ->
      do (cin', zs) <- adder (n - 1) -< (cin, (xs, ys))
         (z, cout) <- fullAdd -< (cin', (x, y))
         returnA -< (cout, z:zs)

-- | Full subber: given a borrow in and two bits, yield their
-- difference and a borrow out.
fullSub :: ArrowComb (~>) => (B (~>), (B (~>), B (~>))) ~> (B (~>), B (~>))
fullSub = proc (borrowIn, ab) ->
      do (r0, b1)  <- halfSub -< ab
         (r,  b2)  <- halfSub -< (r0, borrowIn)
         borrowOut <- orA     -< (b1, b2)
         returnA -< (r, borrowOut)
    where
      halfSub :: ArrowComb (~>) => (B (~>), B (~>)) ~> (B (~>), B (~>))
      halfSub = xorA &&& (first notA >>> andA)

-- | Simple ripple-carry (ripple-borrow?) subber.
subber :: ArrowComb (~>) => Integer -> (B (~>), ([B (~>)], [B (~>)])) ~> (B (~>), [B (~>)])
subber 0 = proc (bin, ([], [])) -> returnA -< (bin, [])
subber n = proc (bin, (x:xs, y:ys)) ->
  do (bin', zs) <- subber (pred n) -< (bin, (xs, ys))
     (z, bout) <- fullSub -< (bin', (x, y))
     returnA -< (bout, z:zs)

-- | Simple multiplier. Compute the partial products (bitwise binary
-- multiplication is simply (/\)) and sum the results.
--
-- We assume that the length of the two input lists is given by the
-- parameter /n/. The output is of length /2n/.
--
-- FIXME following Lava, it's easier to do it LSB -> MSB.
multiplier :: ArrowComb (~>) => Integer -> ([B (~>)], [B (~>)]) ~> [B (~>)]
multiplier n0 =
  case compare n0 0 of
    LT -> error $ "ArithmeticCircuits.multiplier: negative length: " ++ show n0
    EQ -> arr (const [])
    GT -> m' n0
  where
    m' m0 =
      case m0 of
        1 -> proc ([x], ys) ->
          do pp <- (| (mapAC n0) (\y -> andA -< (x, y)) |) ys -- partial product for x (width n0)
             ff <- falseA -< ()
             returnA -< ff : pp -- width n0 + 1 (n = 1)
        n -> proc (x : xs, ys) ->
          do pps <- m' (pred n) -< (xs, ys) -- partial products for xs (width n0 + n - 1)
             pp <- (| (mapAC n0) (\y -> andA -< (x, y)) |) ys -- partial product for x (width n0)
             ff <- falseA -< ()
             let pp' = ff : pp ++ genericReplicate (pred n) ff -- align the partial product (width n0 + n)
                 pps' = ff : pps -- align the partial products (width n0 + n)
             (_cout, p) <- adder (n0 + n) -< (ff, (pp', pps')) -- no carry out as the MSBs are both 0.
             returnA -< p -- width n0 + n

-------------------------------------------------------------------
-- Natural-number specific circuits.
-------------------------------------------------------------------

-- | Generate a bit pattern of the given width, representing the given
-- natural number.
toNat :: (Arrow (~>), Integral n, Show n)
      => Integer -> n -> ((b, b) ~> [b])
toNat width i
--     | trace ("toNat: " ++ show i) false = undefined
  | i < 0 = error $ "ArithmeticCircuits.toNat: negative literal: " ++ show i
  | i > (2 ^ width) - 1 = error $ "ArithmeticCircuits.toNat:  literal too large: " ++ show i
  | otherwise = arr (encNum i [] width)
  where
    encNum 0 s d (ff, _tt) = genericReplicate d ff ++ s
    encNum j s d fftt@(ff, tt) = s `seq`
      encNum (j `div` 2) ((if even j then ff else tt) : s) (d - 1) fftt

-- | 'toNat' in a 'Boolean' context.
toNatBC :: (Boolean b, Integral n, Show n) => Integer -> n -> [b]
toNatBC w n = toNat w n (false, true)

-- | 'toNat' in an 'ArrowComb' context.
toNatAC :: (ArrowComb (~>), Integral n, Show n) => Integer -> n -> (env ~> [B (~>)])
toNatAC w n = note ("toNatAC" ++ show w ++ " " ++ show n) $
                falseA &&& trueA >>> toNat w n

-- | Less-than-or-equal-to on naturals.
leNat :: ArrowComb (~>) => Integer -> ([B (~>)], [B (~>)]) ~> B (~>)
leNat n = note ("leNat" ++ show n) $ proc (x, y) ->
    do bin <- falseA -< ()
       (underflow, _xydiff) <- subber n -< (bin, (x, y))
       orA <<< second (equalA n) -< (underflow, (x, y))

-- | Less-than on naturals.
ltNat :: ArrowComb (~>) => Integer -> ([B (~>)], [B (~>)]) ~> B (~>)
ltNat n = note ("ltNat" ++ show n) $ proc (x, y) ->
    do bin <- falseA -< ()
       (underflow, _xydiff) <- subber n -< (bin, (x, y))
       returnA -< underflow

-- | Add two naturals. On overflow, return the largest representable
-- number.
addNat :: (ArrowComb (~>), ArrowMux (~>) (B (~>)))
       => Integer -> ([B (~>)], [B (~>)]) ~> [B (~>)]
addNat n = note ("addNat" ++ show n) $ proc xy ->
  do cin <- falseA -< ()
     (overflow, xysum) <- adder n -< (cin, xy)
     top <- toNatAC n (2 ^ n - 1 :: Integer) -< ()
     zipWithA n muxA -< (genericReplicate n overflow, zip top xysum)

-- | Subtract two naturals. On underflow, return zero.
subNat :: (ArrowComb (~>), ArrowMux (~>) (B (~>)))
       => Integer -> ([B (~>)], [B (~>)]) ~> [B (~>)]
subNat n = note ("subNat" ++ show n) $ proc xy ->
  do bin <- falseA -< ()
     (underflow, xydiff) <- subber n -< (bin, xy)
     bot <- toNatAC n (0 :: Integer) -< ()
     zipWithA n muxA -< (genericReplicate n underflow, zip bot xydiff)

-- | Multiply two naturals. The output width is twice the width of a
-- single input.
mulNat :: (ArrowComb (~>), ArrowMux (~>) (B (~>)))
        => Integer -> ([B (~>)], [B (~>)]) ~> [B (~>)]
mulNat n = note ("mulNat" ++ show n) $ multiplier n -- FIXME >>> arr (\xs -> trace ("mulNat " ++ show (genericLength xs)) $ assert (genericLength xs == 2 * n) xs)

-- | Cast a natural from one width to another.
castNat :: forall (~>). (ArrowComb (~>), ArrowMux (~>) (B (~>)))
        => Integer -> Integer -> [B (~>)] ~> [B (~>)]
castNat n0 n1 =
  case compare n0 n1 of
    LT -> padA
    EQ -> id
    GT -> truncA
  where
    padA :: [B (~>)] ~> [B (~>)]
    padA = ((falseA >>> arr (genericReplicate (n1 - n0))) &&& id) >>> arr2 (++)
    truncA = arr (genericDrop (n0 - n1))
{-

----------------------------------------
-- Converting from one-hot to binary.
-- FIXME: output size should be 2^input size.
-- Currently we trust the user.
----------------------------------------

oneHotToBinary :: forall arrow b size size' .
                  (Card size, Card size', ArrowComb arrow b)
               => arrow (Vector size b) (Nat size' b)
oneHotToBinary = unVectorA >>> mkOH2B (c2num (undefined :: size) :: Int) >>> arr mkVector >>> natA
    where
      mkOH2B 0 = proc [] -> returnA -< []
      mkOH2B n = proc (x:xs) ->
                   do os <- mkOH2B (pred n) -< xs
                      mkOH2B' (pred n) -< (x, if n `mod` 2 == 0 then x:os else os)

      mkOH2B' 0 = proc (_x, os) -> returnA -< os
      mkOH2B' n = proc (x, o:os) ->
                    do o' <- or2 -< (x, o)
                       os' <- mkOH2B (pred n) -< os
                       returnA -< o':os'
-}
