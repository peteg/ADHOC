module T where

import Tests.KesterelBasis

-- A schizophrenic signal, requiring two wires for correctness.
-- FIXME this shows our environment passing is pretty clunky.
e =
  loopE $
    signalE $ \s ->
      proc x ->
        do v <- (| (presentE s)
                     (nothingE <<< lift trueA -< ()) -- "emit O"
                     (nothingE <<< lift falseA -< ()) |)
           pauseE -< ()
           emitE s -< ()
           lift trueA -< ()
c = idB >>> runE e

prop_correct = property (\xs -> simulate c xs
                             == take (length xs) (repeat (false, true)))
test_constructive = isJust (isConstructive c)

-- The translation doesn't cope with schizophrenia.
-- test_constructive = isNothing (isConstructive c)
