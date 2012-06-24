module T where

import Prelude hiding ( id )
import Tests.ModelCheckerBasis

-- No initial states.
c = proc () ->
  do rec x <- (| unsafeNonDetAC (\x -> falseA -< ()) (idB -< x) |)
     returnA -< x

Just (m, out) = isConstructive c
ctlM = mkCTLModel m

exception_model = ctlM `seq` True
