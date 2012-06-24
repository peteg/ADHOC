-- The model checker objects to no state.
module T where

import Tests.ModelCheckerBasis

c = unitA

Just (m, out) = isConstructive c

-- FIXME these days every model has a boot bit, i.e. there's always state.
ok_model = m
-- exception_stateless = mkCTLModel m
ok_stateless = mkCTLModel m
