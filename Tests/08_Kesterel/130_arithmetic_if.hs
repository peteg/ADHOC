module T where

import Tests.KesterelBasis
import ADHOC.Data.Arithmetic

robot halt = signalE $ \s ->
  loopE $ proc sensor ->
    do x <- (| ifE (geA <<< second (constNat (undefined :: Four) 3) -< (sensor, ()))
                   ( emitE s  <<< emitE halt -< () )
                   ( nothingE -< () ) |)
       pauseE -< ()
       sigE s -< ()

e = signalE robot
c = runE e

prop_correct = property (\xs -> simulate c xs == rhs xs)
    where rhs xs = [ (false, if x >= 3 then true else false) | x <- xs ]
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
