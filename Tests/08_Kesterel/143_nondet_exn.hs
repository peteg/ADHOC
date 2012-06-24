-- Non-deterministically generate a new bit: simplify.
-- FIXME input_process is schizophrenic ???
module T where

import Tests.KesterelBasis

bitP :: ProbeID
bitP = "bit"

input_process bit = loopE $
   (  (loopE_ $ \exn -> emitE bit >>> throwE exn)
    `nondetE`
      (loopE_ $ \exn ->               throwE exn) ) >>> pauseE

top = signalE $ \bit -> probeSigE bitP bit >>> input_process bit

system = unitA >>> runE top

Just (m, (_, ())) = isConstructive system

ctlM = mkCTLModel m

-- The input process behaves.
test_input_process_new = isOK (mc ctlM (ag (ex (probe bitP) /\ ex (neg (probe bitP)))))
