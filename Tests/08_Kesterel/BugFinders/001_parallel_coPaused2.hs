module T where

import Tests.KesterelBasis

-- sync_combine expects both branches to pause.
e = catchE $ \e -> throwE e |||| nothingE

c = arr (\() -> ()) >>> runE e

test_constructive = isJust (isConstructive c)
