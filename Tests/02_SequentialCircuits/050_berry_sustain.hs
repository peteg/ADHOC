-- Berry, "Constructive Semantics for Pure Esterel", p130/131.

module T where

import Tests.Basis

-- Using the basic translation, "sustain s" gets compiled into this
-- (after constant propagation). We can use 'ArrowLoop' as all loops
-- go through delays.

c =
  proc () ->
    do boot <- delayAC trueA falseA -< ()
       rec go <- orA -< (boot, k0)
           k0 <- (| delayAC (falseA -< ()) (returnA -< go) |)
       let s   = go
           k1  = go -- paused
           sel = k0
       returnA -< (s, k1, k0, sel)

prop_correct = property (\xs -> simulate c xs == rhs xs)
    where rhs xs = take (length xs)
                        ((true, true, false, false) : repeat (true, true, true, true))

test_constructive = isJust (isConstructive c)

ok_netlist = runNL c

-- The equivalent circuit:
-- loop (emitS; (nothing || pause))
-- is mis-compiled, leading to a non-constructive circuit.

c' =
  proc () ->
    do boot <- delayAC trueA falseA -< ()
       (k0, fork, y)
           <- (| combLoop (\k0 ->
                do fork <- orA -< (k0, boot)
                   z <- delayAC falseA trueA -< ()
                   y <- orA <<< second (notA <<< orA) -< (z, (z, fork))
                   x <- orA -< (fork, z)
                   k0' <- andA <<< second andA -< (fork, (x, y))
                   returnA -< ((k0', fork, y), k0') ) |)
       k1 <- andA <<< second orA -< (fork, (fork, y))
       let s = fork
       returnA -< (s, k1, k0)

prop_correct' = property (\xs -> simulate c' xs == rhs xs)
    where rhs xs = take (length xs)
                        ((true, true, false) : repeat (bottom, bottom, bottom))

test_constructive' = isNothing (isConstructive c')

ok_netlist' = runNL c'
