-- The identity circuit works. Note this is Control.Category.id

-- This is an exercise in concretising the types.

module T where

import Prelude ()
import Tests.Basis

c :: ArrowComb (~>) => B (~>) ~> B (~>)
c = id

prop_correct = property (\xs -> simulate c xs == xs)
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
