-- Non-deterministically generate a new bit when asked to.
module T where

import Tests.KesterelBasis

bitP, nextBitP :: ProbeID
bitP = "bit"
nextBitP = "next bit"

{-
top = signalE $ \(bit, nextBit) -> probeSigE bitP bit >>> probeSigE nextBitP nextBit >>>
 (  sustainE nextBit
  ||||
    loopE (((sustainE bit `nondetE` haltE) `weak_abortE` nextBit) >>> pauseE))
-}

top = signalE $ \(bit, nextBit) -> probeSigE bitP bit >>> probeSigE nextBitP nextBit >>>
 (  sustainE nextBit
  ||||
    loopE (
--      ((sustainE bit `nondetE` haltE) `weak_abortE` nextBit)
      (catchE $ \e ->
       (    (sustainE bit `nondetE` haltE))
       |||| (loopE (presentE nextBit (throwE e) nothingE >>> pauseE)))
     >>> pauseE))

system = unitA >>> runE top

Just (m, (_, ())) = isConstructive system
ctlM = mkCTLModel m

-- The input process behaves.
test_input_process_new = isOK (mc ctlM (ag (probe nextBitP --> (ex (probe bitP) /\ ex (neg (probe bitP))))))
test_input_process_hold = isOK (mc ctlM (ag (neg (probe nextBitP) --> (probe bitP <-> ax (probe bitP)))))

-- ce = showCounterExample ctlM (ag (probe nextBitP --> (ex (probe bitP) /\ ex (neg (probe bitP)))))

-- The sender always eventually asks (and not) for more bits.
test_input_process_live_more = isOK (mc ctlM (ag (probe nextBitP)))

ok_netlist = runNL system
