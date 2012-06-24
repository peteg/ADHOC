module T where

import Tests.KesterelBasis

-- Loop: inner exception is thrown, signal emitted.
-- FIXME: this is schizophrenic.
ed = signalE $ \s ->
  loopE (catchE (\e1 -> pauseE >>> throwE e1) >>> emitE s) >>> sigE s
cd = unitA >>> runE ed

prop_correct_ed = property (\xs -> simulate cd xs == take (length xs) (zip (repeat false) (false : repeat true)))
test_constructive_ed = isJust (isConstructive cd)

-- ed with the loop body duplicated. Seems to work.
ee = signalE $ \s ->
  let b = catchE (\e1 -> pauseE >>> throwE e1) >>> emitE s
  in loopE (b >>> b) >>> sigE s
ce = unitA >>> runE ee

prop_correct_ee = property (\xs -> simulate ce xs == take (length xs) (zip (repeat false) (false : repeat true)))
test_constructive_ee = isJust (isConstructive ce)
