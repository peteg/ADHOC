-- Non-deterministically generate a new bit at every instant.
module T where

import Tests.KesterelBasis

bitP :: ProbeID
bitP = "bit"

input_process bit =
  loopE ((emitE bit `nondetE` nothingE) >>> pauseE)

top = signalE $ \bit -> probeSigE bitP bit >>> input_process bit

system = unitA >>> runE top

Just (m, (_, ())) = isConstructive system

ctlM = mkCTLModel m

-- We get the full branching structure.
test_input_process_new = isOK (mc ctlM (ag (ex (probe bitP) /\ ex (neg (probe bitP)))))
