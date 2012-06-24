-- Malik's classic f . g or g . f example.
-- FIXME the constructivity combLoop instance limits us to f, g :: BDD -> BDD
-- ... but the definition itself is more general

module T where

import Tests.Basis

fORg :: (ArrowMux (~>) v, ArrowCombLoop (~>) v)
     => (v ~> v) -> (v ~> v) -> ((B (~>), v) ~> v)
fORg f g =
    proc (fg, x) ->
	(| combLoop (\gOut ->
	  do fOut  <- f <<< muxA -< (fg, (x, gOut))
	     gOut' <- g <<< muxA -< (fg, (fOut, x))
	     out   <- muxA       -< (fg, (gOut', fOut))
	     returnA -< (out, gOut'))
	 |)

f = proc a -> do rec x <- (| delayAC (trueA -< ()) (notA -< x) |)
                 andA -< (a, x)
g = proc a -> do rec x <- (| delayAC (trueA -< ())
                                     (| delayAC (trueA -< ()) (notA -< x) |) |)
                 andA -< (a, x)

c  = fORg f g
c' = fORg g f

-- c and c' are not distinguished by fORg.
prop_correct = property (\xs -> simulate c xs == simulate c' xs)

-- what the circuit does for well-defined inputs.
-- FIXME quickcheck bails out if we use ==>. We'd really like a "well defined" generator here.
prop_characterise = property $ \xs' ->
  let xs = filter (\(x, y) -> x /= bottom && y /= bottom) xs'
      t = cycle [true, false, false, false]
      res = [ x /\ y | ((_, x), y) <- zip xs t ]
   in simulate c xs == res

test_constructive = isJust (isConstructive c)
test_constructive' = isJust (isConstructive c')
ok_netlist = runNL c
ok_netlist' = runNL c'
