-- Berry's ABRO example from the Esterel Language Primer (p15).
module T where

import Tests.KesterelBasis

-- | ABRO itself.
abro a b r o =
  proc () ->
    (| (loop_eachE r)
         (do (await_immediateE a -< ()) |||| (await_immediateE b -< ())
             sustainE o -< () ) |)

-- | Circuit interface.
top =
    bool2sig $ \a ->
      bool2sig $ \b ->
        bool2sig $ \r ->
          signalE $ \o ->
      abro a b r o >>> sigE o

c = runE top

-- FIXME correctness: model checker
-- prop_correct = property (\xs -> simulate c0 xs == simulate c1 xs)
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
