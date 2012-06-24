-- 'kTest' needs to be in an 'agent' context.

module T where

import Tests.KBPBasis

c = unitA >>> kTest ("agent" `knows` true)

exception_constructive = isJust (isConstructive c)
