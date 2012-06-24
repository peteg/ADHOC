-- Caught bug: using 'l' rather than 'sl' in the negation of the
-- signal vector 'sv' in presentE.
module T where

import Tests.KesterelBasis

e = signalE $ \s1 -> (presentE s1 nothingE nothingE) |||| nothingE
c = arr (\() -> ()) >>> runE e

test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
