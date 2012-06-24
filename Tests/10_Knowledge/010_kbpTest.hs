-- Very simple KBP.

module T where

import Tests.KBPBasis

kbpt = kTest ("kbp" `knows` probe "boot")
kbp = agent "kbp" kbpt

c = proc () ->
      do boot <- probeA "boot" <<< delayAC falseA trueA -< ()
         kbp -< ()

test_constructive = isJust (isConstructive c)
