module T where

import Tests.KesterelBasis

-- Output trueA while the input is trueA, then terminate.
e = signalE $ \s -> loopE_ $ \e -> proc x ->
      do (| ifE (returnA -< x)
              ( pauseE <<< emitE s -< () )
              -- Make this into a safe loop by adding an unreachable 'pauseE'.
              ( pauseE <<< throwE e -< () ) |)
         sigE s -< ()

c = runE e

-- Straight ADHOC circuit
-- FIXME improve handling of bottom, strengthen property.
c' = proc x ->
       do rec seenFalse <- orA <<< notA *** delayAC falseA returnA -< (x, seenFalse)
              seenFalseBefore <- delayAC falseA returnA -< seenFalse
          seenFalseThisInstant <- andA <<< second notA -< (seenFalse, seenFalseBefore)
          y <- andA <<< first notA -< (seenFalse, x)
          returnA -< (seenFalseThisInstant, y)

prop_correct = property (\xs -> let xs' = map unSimBoolDef xs in simulate c xs' == simulate c' xs')
test_constructive = isJust (isConstructive c)
test_constructive' = isJust (isConstructive c')
ok_netlist = runNL c
ok_netlist' = runNL c'
