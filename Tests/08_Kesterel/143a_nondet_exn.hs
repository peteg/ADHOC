-- Non-deterministically generate a new bit when asked to.
-- FIXME input_process is schizophrenic when nextBit is set two instants in a row ??
module T where

import Tests.KesterelBasis

bitP, nextBitP :: ProbeID
bitP = "bit"
nextBitP = "next bit"

input_process (bit, nextBit) = loopE $ emitE nextBit >>>
   (  (loopE_ $ \exn -> emitE bit >>> presentE nextBit (throwE exn) pauseE)
    `nondetE`
      (loopE_ $ \exn ->               presentE nextBit (throwE exn) pauseE) ) >>> pauseE

top = signalE $ \s@(bit, nextBit) -> probeSigE bitP bit >>> probeSigE nextBitP nextBit >>>
    input_process s

system = unitA >>> runE top

Just (m, (_, ())) = isConstructive system

ctlM = mkCTLModel m

test_input_process_new = isOK (mc ctlM (ag (probe nextBitP --> (ex (probe bitP) /\ ex (neg (probe bitP))))))
test_input_process_new' = isOK (mc ctlM (ag (ex (probe bitP) /\ ex (neg (probe bitP)))))
test_always_eventually_new = isOK (mc ctlM (ag (ef (probe nextBitP))))
