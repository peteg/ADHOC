module T where

import Tests.KesterelBasis

-- |||| demands coPaused and shouldn't be.
e = nothingE |||| pauseE

c = arr (\() -> ()) >>> runE e

test_constructive = isJust (isConstructive c)
