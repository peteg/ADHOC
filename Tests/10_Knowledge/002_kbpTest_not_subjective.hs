-- The knowledge formula must be subjective.

module T where

import Tests.KBPBasis

c = unitA >>> (agent "agent" $ kTest ("some other agent" `knows` true))

exception_constructive = isJust (isConstructive c)
