{-# LANGUAGE Arrows, FlexibleContexts, NoMonomorphismRestriction, RankNTypes, ScopedTypeVariables, TypeOperators #-}
{- Synthesis of cache protocols from KBPs.
 - Copyright   :  (C)opyright 2011, 2012 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)

This model satisfies "independent initialisation".

A more realistic write-once cache. Flushing is still problematic.

We optimise for bus operations here, not the amount of state the cache
controller has to maintain per cache line.

FIXME

why is cache2 different from cache1? -- why does stamina explode on 2 but not 1?
we can replace the processors with smaller FSMs written in ADHOC - should reduce the state by ~ 4 * 2 bits.

-}
module Main where

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

-- A "probed" register.
registerPE :: (EC (~>), ArrowProbe (~>) (B (~>)))
           => ProbeID
           -> ((Signal, Signal, Signal) -> E (~>) () ())
           -> E (~>) () ()
registerPE pid f = registerE $ \sigs@(_reg_set, _reg_reset, reg_val) ->
  probeSigE pid reg_val >>> f sigs

-- A "probed" delayed register.
register_delayedPE :: (EC (~>), ArrowProbe (~>) (B (~>)))
           => ProbeID
           -> ((Signal, Signal, Signal) -> E (~>) () ())
           -> E (~>) () ()
register_delayedPE pid f = register_delayedE $ \sigs@(_reg_set, _reg_reset, reg_val) ->
  probeSigE pid reg_val >>> f sigs

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
cache_ownerP, mem_readP, mem_writeP, mem_valP, mem_reg_valP :: ProbeID
cache_ownerP = "co"
mem_readP = "mr"
mem_writeP = "mw"
mem_valP = "mv"
mem_reg_valP = "mrv"

-- | The memory:
--
-- - stores the bit whenever a cache does a write.
-- - responds with the value of the bit whenever a cache does a read and no other cache responds.
--
-- FIXME the read path has not been tested by Cache-simple.
-- FIXME the initial memory register value should be non-det.
--
-- FIXME register delayed or immediate?
-- Note that the effect on memory occurs in the instant after the
-- signal. This keeps the memory in sync with the cache controllers.
memory :: (EC (~>), ArrowProbe (~>) (B (~>)))
       => (Signal, Signal, Signal, Signal) -> E (~>) () ()
memory (cache_owner, mem_read, mem_write, mem_val) =
  probeSigE cache_ownerP cache_owner >>>  probeSigE mem_readP mem_read >>> probeSigE mem_writeP mem_write >>> probeSigE mem_valP mem_val >>> (
  registerPE mem_reg_valP $ \(reg_set, reg_reset, reg_val) ->
    ( loopE $ sig_caseE
      [ sigE mem_read
          :-     pauseE -- "read"
             >>> presentE cache_owner
                   (presentE mem_val (emitE reg_set) (emitE reg_reset)) -- Cache claims ownership, record what it says
                   (whenE reg_val (emitE mem_val)) -- Caches silent, emit our value
      , sigE mem_write :- presentE mem_val (emitE reg_set) (emitE reg_reset)
      ] >>> pauseE ) )

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

processor :: (EC (~>), ArrowNonDet (~>) (B (~>)), ArrowProbe (~>) (B (~>)))
          => Integer -> (Signal, Signal, Signal, Signal) -> E (~>) () ()
processor i (proc_read, proc_write, proc_val, proc_cache_op_finished) =
      probeSigE (proc_readP i) proc_read >>> probeSigE (proc_writeP i) proc_write
  >>> probeSigE (proc_valP i) proc_val >>> probeSigE (proc_cofP i) proc_cache_op_finished
  >>> let procOp =
{-
               -- Local operation
               nothingE
            `nondetE`
               -- Memory operation: read
               (loopE_ $ \exn -> emitE proc_read >>> whenE proc_cache_op_finished (throwE exn) >>> pauseE)
            `nondetE`
               -- Memory operation: write 0.
               (loopE_ $ \exn -> emitE proc_write                    >>> whenE proc_cache_op_finished (throwE exn) >>> pauseE)
            `nondetE`
               -- Memory operation: write 1.
               (loopE_ $ \exn -> emitE proc_write >>> emitE proc_val >>> whenE proc_cache_op_finished (throwE exn) >>> pauseE)
-}
               (loopE_ $ \exn -> emitE proc_write                    >>> whenE proc_cache_op_finished (throwE exn) >>> pauseE)
      in procOp -- loopE (procOp >>> pauseE)

-------------------------------------------------------------------

-- Caches

c_knowsP, cline_valueP :: Integer -> ProbeID
c_knowsP i = "ck" ++ show i
cline_valueP i = "cval" ++ show i
cline_dirtyP i = "cdirty" ++ show i

-- | Cache @i@ knows the bit in memory, or the bit in the dirty cache
-- if there is one.
owner_val i pol = cache i `knows`
  (   conjoin [ probe (cline_dirtyP j) --> pol (probe (cline_valueP j)) | j <- caches ]
  /\ (conjoin [ neg (probe (cline_dirtyP j)) | j <- caches ] --> pol (probe mem_reg_valP)) )

-- | Does this cache know the value of the cache line?
cache_knows i cache_does_know cache_val_set cache_val_reset =
      probeSigE (c_knowsP i) cache_does_know
  >>> kTestE (owner_val i id)
        (emitE cache_does_know >>> emitE cache_val_set)
        (kTestE (owner_val i neg)
           (emitE cache_does_know >>> emitE cache_val_reset)
           nothingE)

-- | Respond to a memory read request if we're dirty.
--
-- This cleans the cache.
-- FIXME is the condition is_dirty or cache_does_know? -- is_dirty == owner, knows is stronger.
cache_respond_if_owner cache_owner mem_read mem_val cache_val clean is_dirty =
  loopE $
    whenE mem_read
      (whenE is_dirty
         (emitE cache_owner
      >>> whenE cache_val (emitE mem_val)
      >>> pauseE >>> emitE clean)) -- Clean in the next instant.
    >>> pauseE

-- | Unconditional bus operation.
--
-- Wait for the bus. Execute @op@.
busOp (req, ack) op =
  sustain_whileE req $
    loopE_ (\exn -> whenE ack (throwE exn) >>> pauseE) >>> op

-- | Guarded bus operation.
--
-- Wait for the bus. If @cond@ becomes true before we acquire the bus
-- then do nothing, otherwise execute @op@.
guardedBusOp (req, ack) cond op =
  sustain_whileE req $
    loopE_ $ \exn -> presentE cond
                        (throwE exn)
                        (whenE ack (op >>> throwE exn))
                      >>> pauseE

cacheController i -- cache number
  (cache_owner, mem_read, mem_write, mem_val) -- bus signals
  busArb -- bus arbitration
  (proc_read, proc_write, proc_val, proc_cache_op_finished) -- processor signals
  = registerPE (cline_valueP i) $ \(cache_val_set, cache_val_reset, cache_val) ->
    registerPE (cline_dirtyP i) $ \(dirty, clean, is_dirty) ->
    signalE $ \cache_does_know ->
        (loopE $ cache_knows i cache_does_know cache_val_set cache_val_reset >>> pauseE)
      ||||
        cache_respond_if_owner cache_owner mem_read mem_val cache_val clean is_dirty
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
                            emitE mem_read >>> pauseE -- Indicate we want to read.
                        >>> pauseE)) -- Wait for a response from memory or another cache.
                   >>> whenE cache_val (emitE proc_val) -- The kTest takes care of the response.
                   >>> emitE proc_cache_op_finished
              -- Write through on the first write, local operation thereafter.
            , sigE proc_write
                :- presentE is_dirty
                     -- Write hit (local)
                     nothingE
                     -- Write miss (bus)
                     (busOp busArb (
                         {- FIXME we need to do a read here. We might get away with a guardedBusOp: if we know the memory is up to date we can skip straight to writing.
                         The point is to force any dirty cache to do a write back
                         I think we can do a read-write as a single bus operation.
                         But perhaps it doesn't matter too much. -}
                            emitE mem_read >>> pauseE -- Indicate we want to read.
                        >>> pauseE -- Wait for a response from memory or another cache.
                        >>> emitE dirty -- FIXME timing: this cache is dirty in the next instant.
                        >>> emitE mem_write >>> whenE proc_val (emitE mem_val)) )
                   >>> presentE proc_val (emitE cache_val_set) (emitE cache_val_reset)
                   >>> emitE proc_cache_op_finished
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
    procs busSigs = ( (mkSizedListf $ \i -> (cache i, proc_cache i busSigs)) `withLength` (undefined :: Caches)
                    , memory busSigs)

m :: Model BDD
ctlM :: CTLModel BDD
-- Just (_, m, _) = broadcastSprSynthII' MinNone system
Just (_, m, _) = broadcastSprSynthII' MinBisim system
-- Just (_, m, _) = broadcastSprSynthII' MinSTAMINA system
ctlM = mkCTLModel m

-------------------------------------------------------------------
-- Specifications
-------------------------------------------------------------------

specs :: (Boolean b, Eq b) => [Spec b]
specs =
  [
    sOK "the caches always know the cache line" $ ag (conjoin
       [ probe (c_knowsP i) | i <- caches ])

  , sOK "if the cache is dirty then the processor knows the cache line" $ ag (conjoin
       [ probe (cline_dirtyP i) --> probe (c_knowsP i)
       | i <- caches ])

  , sOK "processor writes 1 eventually bus sees a write of 1" $ ag (conjoin
       [ (probe (proc_writeP i) /\ probe (proc_valP i))
           --> af (probe mem_writeP /\ probe mem_valP)
       | i <- caches ])
    -- Expect this to fail due to local writes (dirtiness)

    -- FIXME is this right/general enough?
  , sOK "cache coherence write 1" $ ag (conjoin
       [ (probe (proc_writeP i) /\ probe (proc_valP i) /\ probe (proc_cofP i))
           --> ax ( (conjoin [ (probe (proc_readP j) /\ probe (proc_cofP j)) --> probe (proc_valP j)
                          | j <- caches ])
                    `au_unbounded` probe mem_writeP) -- FIXME note next bus write event.
       | i <- caches ])
  , sOK "dirtiness is sometimes possible" $ conjoin [ ef (probe (cline_dirtyP i)) | i <- caches ]
  , sOK "dirtiness is always possible" $ ag (conjoin [ ef (probe (cline_dirtyP i)) | i <- caches ])
  , sOK "dirtiness is exclusive" $ ag (conjoin
      [ probe (cline_dirtyP i) --> conjoin [ neg (probe (cline_dirtyP j))
                                           | j <- caches, j /= i ]
      | i <- caches ])

    -- The processors engage in some activity.
  , sOK "procs can infinitely often read" $ ag (conjoin [ ef (probe (proc_readP i)) | i <- caches ])
  , sOK "procs can infinitely often write" $ ag (conjoin [ ef (probe (proc_writeP i)) | i <- caches ])

    -- The memory can always take on different values.
  , sOK "mem_reg can always become 0" $ ag (ef (neg (probe mem_reg_valP)))

  , sOK "mem_reg can always become 1" $ ag (ef (probe mem_reg_valP))

    -- The bus is infinitely often active.
    -- Not true in the absence of fairness constraints.
  , sFail "the bus is infinitely often active (fails)" $ ag (af (probe mem_writeP \/ probe mem_readP))

    -- ... but it is always possible for there to be more activity.
  , sOK "test_busActive_write" $ ag (ef (probe mem_writeP))
  , sOK "test_busActive_write_0" $ ag (ef (probe mem_writeP /\ probe mem_valP))
  , sOK "test_busActive_write_1" $ ag (ef (probe mem_writeP /\ neg (probe mem_valP)))

    -- It is also always possible for the bus to be idle.
  , sOK "the bus can always be idle in the future" $ ag (ef (neg (probe mem_writeP) /\ neg (probe mem_readP)))

    -- Caches can do local writes privately.
  , sFail "caches always know (fails)" $ ag (conjoin [ probe (c_knowsP i) | i <- caches ])

  , sFail "no read actions (fails)" $ ag (neg (probe mem_readP))
  ]

test_specs = dynamicReordering ReorderStableWindow3 >> mcce ctlM specs
