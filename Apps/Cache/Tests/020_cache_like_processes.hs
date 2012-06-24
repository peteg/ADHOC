-- Test the arbitrated bus with processes that look like the cache controllers.
module T where

import Data.Maybe ( isJust )
import System.Mem ( performGC )

import Broadcast

import ADHOC hiding ( tt )
import ADHOC.NonDet
import ADHOC.Control.Kesterel

import ADHOC.ModelChecker.CTL as CTL
import ADHOC.ModelChecker.CounterExamples

-- Test process.

-- Explodes for three processes (at least without dynamic BDD variable reordering)
-- type Processes = Three
type Processes = Two

numProcesses :: Integer
numProcesses = c2num (undefined :: Processes)

processes :: [Integer]
processes = [1 .. numProcesses]

reqP, ackP :: Integer -> ProbeID
reqP i = "req" ++ show i
ackP i = "ack" ++ show i

procAID :: Integer -> AgentID
procAID i = "proc" ++ show i

-- The process making the requests is pick-and-stick: it continues to
-- request access until it is granted. It only requests a single
-- instant.
--
-- Note we probably shouldn't assume fairness here: the processor can
-- do whatever it likes.
process i (req, ack) =
      probeSigE (reqP i) req
  >>> probeSigE (ackP i) ack
  >>> loopE ( (nothingE `nondetFairE` write `nondetFairE` read) >>> pauseE)
  where
    wait_ack = loopE_ $ \exn -> (emitE req >>> presentE ack (throwE exn) nothingE >>> pauseE)

    preq = emitE req >>> pauseE

    read = wait_ack
       >>> preq {- "read" -} >>> preq {- wait -} >>> preq {- get result -}

    write = wait_ack
        >>> preq {- "write" -} >>> preq {- write value -}

system = arbitratedBus procs
  where
    procs () = ( mkSizedListA [ (procAID i, process i) | i <- processes ] `withLength` (undefined :: Processes)
               , nothingE )

Just (m, _) = isConstructive system
ctlM = mkCTLModel m

-- The model is big enough that we need variable reordering.
test_reordering = dynamicReordering ReorderSift >> return True

-- Each process tries to enter its critical region infinitely often.
test_process_live = isOK (mc ctlM (conjoin [ ag (af (probe (reqP i))) | i <- processes ]))

-- At most one process gets ack'ed at a time.
test_mutual_exclusion = isOK (mc ctlM (ag (neg (disjoin
  [ probe (ackP i) /\ probe (ackP j) | i <- processes, j <- [succ i .. numProcesses] ]))))

-- The process is eventually granted access after every request.
-- This is weak fairness with this particular process.
test_deadlock_freedom = isOK (mc ctlM (conjoin
  [ ag (probe (reqP i) --> af (probe (ackP i))) | i <- processes ]))

ce_deadlock_freedom = showCounterExample ctlM (ag (conjoin
  [ probe (reqP i) --> af (probe (ackP i)) | i <- processes ]))

-- No strict sequencing.
test_no_strict_sequencing = isOK (mc ctlM (ag (conjoin
  [ af (ai /\ (ai `eu` (conjoin [ neg (probe (ackP j)) | j <- processes ] `eu` ai)))
    | i <- processes, let ai = probe (ackP i) ])))

-- No ack without a request.
test_no_req_no_ack = isOK (mc ctlM (ag (conjoin [ neg ai `au` ri
    | i <- processes,
      let ai = probe (ackP i)
          ri = probe (reqP i) ])))

-- Ack stays high as long as the request does.
test_ack_while_req = isOK (mc ctlM (ag (conjoin [ neg ai `au` (ri /\ ai `au` neg ri)
    | i <- processes,
      let ai = probe (ackP i)
          ri = probe (reqP i) ])))

test_gc = performGC >> return True
