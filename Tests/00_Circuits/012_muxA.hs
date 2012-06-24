-- The multiplexer circuit works.

module T where

import Tests.Basis

m f g = arr (\x -> (x, ((), ())))
        >>> second (f *** g)
        >>> muxA

c  = m falseA trueA
c' = notA >>> m trueA falseA

prop_correct = property (\xs -> simulate c xs == simulate c' xs)
test_constructive = isJust (isConstructive c)
ok_netlist = runNL c
