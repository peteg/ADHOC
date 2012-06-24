-- Non-deterministically generate a new bit when asked to.
module T where

import Tests.KesterelBasis hiding (weak_abortE)

bitP, nextBitP :: ProbeID
bitP = "bit"
nextBitP = "next bit"

weak_abortE p s = catchE $ \e ->
  (p >>> throwE e) |||| (loopE (presentE s (throwE e) nothingE >>> pauseE))

-- It seems to work if we shuffle things around...
input_process (bit, nextBit) =
    loopE (((sustainE bit `nondetE` haltE) `weak_abortE` nextBit) >>> pauseE)

top = signalE $ \s@(bit, nextBit) -> probeSigE bitP bit >>> probeSigE nextBitP nextBit >>>
  ( loopE ((nothingE `nondetE` emitE nextBit) >>> pauseE)
  ||||
    input_process s )

system = unitA >>> runE top

Just (m, (_, ())) = isConstructive system

ctlM = mkCTLModel m

-- The input process behaves.
test_input_process_new = isOK (mc ctlM (ag (probe nextBitP --> (ex (probe bitP) /\ ex (neg (probe bitP))))))
test_input_process_hold = isOK (mc ctlM (ag (neg (probe nextBitP) --> (probe bitP <-> ax (probe bitP)))))

-- ce = showCounterExample ctlM (ag (probe nextBitP --> (ex (probe bitP) /\ ex (neg (probe bitP)))))

-- The sender always eventually asks (and not) for more bits.
test_input_process_live_more = isOK (mc ctlM (ag (ef (probe nextBitP))))
test_input_process_live_stop = isOK (mc ctlM (ag (ef (neg (probe nextBitP)))))
