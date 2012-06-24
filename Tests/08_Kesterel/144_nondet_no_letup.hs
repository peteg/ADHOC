-- Non-deterministically generate a new bit when asked to.
-- FIXME input_process is schizophrenic when nextBit is set two instants in a row ??
module T where

import Tests.KesterelBasis

bitP, nextBitP :: ProbeID
bitP = "bit"
nextBitP = "next bit"

input_process (bit, nextBit) = loopE $
   (  (loopE_ $ \exn -> emitE bit >>> presentE nextBit (throwE exn) pauseE)
    `nondetE`
      (loopE_ $ \exn ->               presentE nextBit (throwE exn) pauseE) ) >>> pauseE

top = signalE $ \s@(bit, nextBit) -> probeSigE bitP bit >>> probeSigE nextBitP nextBit >>>
  ( loopE (emitE nextBit >>> pauseE)
  ||||
    input_process s )

system = unitA >>> runE top

Just (m, (_, ())) = isConstructive system

ctlM = mkCTLModel m

-- The input process behaves.
test_input_process_new = isOK (mc ctlM (ag (probe nextBitP --> (ex (probe bitP) /\ ex (neg (probe bitP))))))
test_input_process_hold = isOK (mc ctlM (ag (neg (probe nextBitP) --> (probe bitP <-> ax (probe bitP)))))

-- The sender always eventually asks for more bits.
test_always_eventually_new = isOK (mc ctlM (ag (ef (probe nextBitP))))
-- test_always_branching_new = isOK (mc ctlM (ag (ex (probe nextBitP) /\ ex (neg (probe nextBitP)))))
