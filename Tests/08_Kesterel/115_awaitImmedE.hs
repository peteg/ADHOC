-- A simplification of Berry's ABRO example from the Esterel Language Primer (p15).
module T where

import Tests.KesterelBasis

half_abro a r o = proc () ->
    (| (loop_eachE r)
         ( do await_immediateE a -< ()
              sustainE o -< () ) |)

-- | Circuit interface.
top =
    bool2sig $ \a ->
      bool2sig $ \r ->
        signalE $ \o ->
      half_abro a r o >>> sigE o

c = runE top

-- prop_correct = property (\xs -> simulate c0 xs == simulate c1 xs) FIXME
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
