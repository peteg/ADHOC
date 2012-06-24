module T where

import Tests.KesterelBasis

-- This should be the same as never aborting.
e = signalE $ \(x, y, z) ->
  ( (loopE (sustainE x `weak_abortE` y >>> pauseE) >>> emitE z)
    ||||
    loopE (emitE y >>> pauseE >>> pauseE) )
  >>> (sigE x &&& sigE y &&& sigE z)

c = unitA >>> runE e

prop_correct = property (\as -> simulate c as == take (length as) (zip (repeat false) (zip xs (zip ys zs))))
  where
    xs = repeat true
    ys = cycle [true, false]
    zs = repeat false
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
