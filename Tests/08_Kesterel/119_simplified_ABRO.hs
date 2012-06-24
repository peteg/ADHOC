-- A simplification of Berry's ABRO example from the Esterel Language Primer (p15).
module T where

import Tests.KesterelBasis

half_abro a r o =
  proc () ->
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

ok_netlist = dotNL "circ.dot" c
-- FIXME don't do any constant folding here, we're just checking Kesterel.
-- ok_netlist_opt = dot "circ_opt.dot" (runNL (runNL' (runCF c)))
-- main = ok_netlist_opt
