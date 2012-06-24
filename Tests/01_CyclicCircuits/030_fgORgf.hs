-- Malik's classic f . g or g . f example.
-- FIXME the constructivity combLoop instance limits us to f, g :: BDD -> BDD
-- ... but the definition itself is more general

module T where

import Prelude ()
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

f = id
g = notA

c  = fORg f g
c' = fORg g f

prop_correct = property (\xs -> simulate c xs == simulate c' xs)
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
