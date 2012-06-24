module T where

import Tests.KesterelBasis

-- Inner exception is thrown, signal emitted.
ea = signalE $ \s ->
  (catchE (\e0 -> (catchE (\e1 -> pauseE >>> throwE e1) >>> emitE s))) >>> sigE s
ca = unitA >>> runE ea

prop_correct_ea = property (\xs -> simulate ca xs == take (length xs) (zip (false : true : repeat false) (false : true : repeat false)))
test_constructive_ea = isJust (isConstructive ca)

-- Outer exception is thrown, signal not emitted.
eb = signalE $ \s ->
  (catchE (\e0 -> (catchE (\e1 -> pauseE >>> throwE e0) >>> emitE s))) >>> sigE s
cb = unitA >>> runE eb

prop_correct_eb = property (\xs -> simulate cb xs == take (length xs) (zip (false : true : repeat false) (repeat false)))
test_constructive_eb = isJust (isConstructive cb)

-- Loop: outer exception is thrown, signal not emitted.
ec = signalE $ \s ->
  loopE (catchE (\e0 -> (catchE (\e1 -> pauseE >>> throwE e0) >>> emitE s))) >>> sigE s
cc = unitA >>> runE ec

prop_correct_ec = property (\xs -> simulate cc xs == take (length xs) (zip (repeat false) (repeat false)))
test_constructive_ec = isJust (isConstructive cc)
