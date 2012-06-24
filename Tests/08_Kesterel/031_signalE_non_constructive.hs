-- A non-constructive program using local signals.
module T where

import Tests.KesterelBasis

e =
  signalE $ \s1 ->
    signalE $ \s2 ->
      ( presentE s1
          (nothingE)
          (emitE s2) )
   ||||
      ( presentE s2
          ( presentE s1
              (nothingE)
              (emitE s1) )
          (nothingE) )

c = unitA >>> runE e

test_constructive = isNothing (isConstructive c)
ok_netlist = runNL c
