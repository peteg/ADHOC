{-# LANGUAGE Arrows, FlexibleContexts, NoMonomorphismRestriction, RankNTypes, ScopedTypeVariables, TypeOperators #-}
{- Synthesis of cache protocols from KBPs.
 - Copyright   :  (C)opyright 2011, 2012 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)

This model satisfies "independent initialisation".

An overly simple write-through cache: there is no flush and no notion
of dirtiness, so each cache always knows the bit. In other words there
is never a read miss.

-}
module Main ( main ) where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude hiding ( (.), id )
import qualified Data.Map as Map

import ADHOC
import ADHOC.NonDet

import ADHOC.Control.Kesterel

import ADHOC.Knowledge

import ADHOC.ModelChecker.CTL as CTL
import ADHOC.ModelChecker.CounterExamples

import Broadcast

-------------------------------------------------------------------
-- Scenario
-------------------------------------------------------------------

cache :: Integer -> AgentID
cache i = "cache" ++ show i

type Caches = Two

caches :: [Integer]
caches = [ 1 .. c2num (undefined :: Caches) ]

-------------------------------------------------------------------

-- | Bus signals.
mem_readP, mem_writeP, mem_valP, mem_reg_valP :: ProbeID
mem_readP = "mr"
mem_writeP = "mw"
mem_valP = "mv"
mem_reg_valP = "mrv"

-- | The memory:
--
-- - stores the bit whenever a cache does a write.
-- - responds with the value of the bit whenever a cache does a read
--
-- Note that the effect on memory occurs in the instant after the
-- signal. This keeps the memory in sync with the cache controllers.
memory :: (EC (~>), ArrowProbe (~>) (B (~>)))
       => (Signal, Signal, Signal) -> E (~>) () ()
memory (mem_read, mem_write, mem_val) =
  register_delayedE mem_reg_valP $ \(reg_set, reg_reset, reg_val) ->
    ( loopE $ sig_caseE
      [ sigE mem_read :- whenE reg_val (emitE mem_val)
      , sigE mem_write :- presentE mem_val (emitE reg_set) (emitE reg_reset)
      ] >>> pauseE )

-------------------------------------------------------------------

-- Processors

{-

A processor can non-deterministically:

- do some local computation
- read from the shared bit
- write to the shared bit

These last two operations are blocking.

We hope to write a spec at the level of what the cache tells the
processor.

-}

proc_readP, proc_writeP, proc_valP, proc_cofP :: Integer -> ProbeID
proc_readP i = "pr" ++ show i
proc_writeP i = "pw" ++ show i
proc_valP i = "pv" ++ show i
proc_cofP i = "pcof" ++ show i

-- processor :: (EC (~>), ArrowUnsafeNonDet (~>) (B (~>)), ArrowProbe (~>) (B (~>)))
--           => Integer -> (Signal, Signal, Signal, Signal) -> E (~>) () ()
processor i (proc_read, proc_write, proc_val, proc_cache_op_finished) =
  probeSigE (proc_readP i) proc_read >>> probeSigE (proc_writeP i) proc_write >>> probeSigE (proc_valP i) proc_val >>> probeSigE (proc_cofP i) proc_cache_op_finished >>>
  loopE ( (
            -- Local operation
            nothingE
         `nondetE`
            -- Memory operation: read
            (loopE_ $ \exn -> emitE proc_read >>> whenE proc_cache_op_finished (throwE exn) >>> pauseE)
         `nondetE`
            -- Memory operation: write 0.
            (loopE_ $ \exn -> emitE proc_write >>> whenE proc_cache_op_finished (throwE exn) >>> pauseE)
         `nondetE`
            -- Memory operation: write 1.
            (loopE_ $ \exn -> emitE proc_write >>> emitE proc_val >>> whenE proc_cache_op_finished (throwE exn) >>> pauseE)
          ) >>> pauseE )

-------------------------------------------------------------------

-- Caches

c_knowsP, cline_valueP :: Integer -> ProbeID
c_knowsP i = "ck" ++ show i
cline_valueP i = "cval" ++ show i

-- | The cache knows the value of the bit in memory.
cache_knows i cache_does_know cache_val_set cache_val_reset = probeSigE (c_knowsP i) cache_does_know >>>
  kTestE (cache i `knows` (probe mem_reg_valP))
    (emitE cache_does_know >>> emitE cache_val_set)
    (kTestE (cache i `knows` (neg (probe mem_reg_valP)))
       (emitE cache_does_know >>> emitE cache_val_reset)
       nothingE)

-- | Unconditional bus operation.
--
-- Wait for the bus. Execute @op@.
busOp (req, ack) op =
  sustainWhileE req $
    loopE_ (\exn -> whenE ack (throwE exn) >>> pauseE) >>> op

-- | Guarded bus operation.
--
-- Wait for the bus. If @cond@ becomes true before we acquire the bus
-- then do nothing, otherwise execute @op@.
guardedBusOp (req, ack) cond op =
  sustainWhileE req $
    loopE_ $ \exn -> presentE cond
                        (throwE exn)
                        (whenE ack (op >>> throwE exn))
                      >>> pauseE

cacheController i -- cache number
  (mem_read, mem_write, mem_val) -- bus signals
  busArb -- bus arbitration
  (proc_read, proc_write, proc_val, proc_cache_op_finished) -- processor signals
  = registerE (cline_valueP i) $ \(cache_val_set, cache_val_reset, cache_val) ->
    signalE $ \cache_does_know ->
        ( loopE $ cache_knows i cache_does_know cache_val_set cache_val_reset >>> pauseE)
      ||||
        -- Processor request.
        ( loopE $ sig_caseE
            [ -- Read
              sigE proc_read
                :- presentE cache_does_know
                     -- Read hit (local)
                     nothingE
                     -- Read miss (bus)
                     (guardedBusOp busArb cache_does_know (
                         emitE mem_read >>> pauseE)) -- Indicate we want to read, and wait for memory to respond.
                     >>> whenE cache_val (emitE proc_val) -- The kTest takes care of the response.
                     >>> emitE proc_cache_op_finished
              -- Write through.
            , sigE proc_write
                :- (busOp busArb $
                            emitE mem_write
                        >>> whenE proc_val (emitE mem_val))
                    >>> emitE proc_cache_op_finished -- FIXME could probably bail out earlier.
              -- No activity from the processor.
              -- In a more complete model we'd do a flush here.
            ] >>> pauseE )

-------------------------------------------------------------------

-- Composition.

proc_cache i busSigs busArb = signalE $ \procSigs ->
    processor i procSigs
  ||||
    cacheController i busSigs busArb procSigs

system = arbitratedBus procs
  where
    probes (mem_read, mem_write, mem_val) =
            probeSigE mem_readP mem_read
        >>> probeSigE mem_writeP mem_write >>> probeSigE mem_valP mem_val

    procs busSigs = ( probes busSigs
                    , (mkSizedListf $ \i -> (cache i, proc_cache i busSigs)) `withLength` (undefined :: Caches)
                    , memory busSigs)

m :: Model BDD
ctlM :: CTLModel BDD
Just (kautos, m, _) = broadcastSprSynthII MinSTAMINA system
ctlM = mkCTLModel m

-------------------------------------------------------------------
-- Specifications
-------------------------------------------------------------------

specs :: (Boolean b, Eq b) => [Spec b]
specs =
  [
    -- The memory can always take on different values.
    sOK "test_mem_reg_val_0" $ ag (ef (neg (probe mem_reg_valP)))
  , sOK "test_mem_reg_val_1" $ ag (ef (probe mem_reg_valP))

    -- The bus is infinitely often active.
    -- Not true in the absence of fairness constraints.
  , sFail "test_busActive_fail" $ ag (af (probe mem_writeP \/ probe mem_readP))

    -- ... but it is always possible for there to be more activity.
  , sOK "test_busActive_write" $ ag (ef (probe mem_writeP))
  , sOK "test_busActive_write_0" $ ag (ef (probe mem_writeP /\ probe mem_valP))
  , sOK "test_busActive_write_1" $ ag (ef (probe mem_writeP /\ neg (probe mem_valP)))

    -- It is also infinitely often possible for the bus to be idle.
  , sOK "bus passive infinitely often" $ ag (ef (neg (probe mem_writeP) /\ neg (probe mem_readP)))

    -- The processors engage in some activity.
  , sOK "procs can infinitely often read" $ ag (conjoin [ ef (probe (proc_readP i)) | i <- caches ])
  , sOK "procs can infinitely often write" $ ag (conjoin [ ef (probe (proc_writeP i)) | i <- caches ])

    -- The caches always know the value of the memory bit as all
    -- memory traffic is public.
  , sOK "caches always know" $ ag (conjoin [ probe (c_knowsP i) | i <- caches ])

    -- For this reason there are no read actions.
  , sOK "no read actions" $ ag (neg (probe mem_readP))

    -- Coherence: the processors always reads the memory bit.
  , sOK "cache coherence" $ ag (conjoin
       [ (probe (proc_readP i) /\ probe (proc_cofP i)) --> (probe (proc_valP i) <-> probe mem_reg_valP)
       | i <- caches ])
  , sOK "cache coherence non trivial" $ ag (conjoin
       [ ef (probe (proc_readP i) /\ probe (proc_cofP i))
       | i <- caches ])

    -- Coherence: The processors always reads the last-written value.
    -- cache i completes a write, and cache j reads at some later
    -- point but before another write occurs.

    -- FIXME think through the timing some more: when can the first read occur? How about the next write?

  , sOK "cache coherence write 1" $ ag (conjoin
       [ (probe (proc_writeP i) /\ probe (proc_valP i) /\ probe (proc_cofP i))
           --> ax ( (conjoin [ (probe (proc_readP j) /\ probe (proc_cofP j)) --> probe (proc_valP j)
                          | j <- caches ])
                    `au_unbounded` probe mem_writeP) -- FIXME note next bus write event.
       | i <- caches ])
  ]

-------------------------------------------------------------------

main :: IO ()
main =
  do -- dynamicReordering ReorderStableWindow3 -- ReorderSiftSym -- ReorderStableWindow3 -- ReorderSift -- ReorderStableWindow3
     m `seq` putStrLn "System is constructive!"
     bddPrintInfo
     m `seq` putStrLn "Synthesis completed!"
     dot kautos
     putStrLn $ "Checking properties..."
     _ <- mcce ctlM specs
     return ()
