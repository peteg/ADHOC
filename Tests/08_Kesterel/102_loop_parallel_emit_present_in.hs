module T where

import Tests.KesterelBasis

e = arr (\x -> ((), x))
      >>> loopE (bool2sig $ \s -> (emitE s |||| nothingE) >>> pauseE >>> sigE s)
c = runE e

prop_correct = property (\xs -> let xs' = map unSimBoolDef xs in
                         simulate c xs'
                      == take (length xs') (zip (repeat false) (repeat true) ) )
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
