-- Non-deterministically choose a bit at time 0.
module T where

import Tests.KesterelBasis

bitP :: ProbeID
bitP = "bit"

top = signalE $ \bit -> probeSigE bitP bit >>> sustainE bit `nondetE` haltE

system = unitA >>> runE top

Just (m, (_, ())) = isConstructive system

ctlM = mkCTLModel m

-- The signal is constant for all time.
test_input_bit_const = isOK (mc ctlM (ag (probe bitP) \/ ag (neg (probe bitP))))
