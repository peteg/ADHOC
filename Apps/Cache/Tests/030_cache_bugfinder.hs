{-# LANGUAGE Arrows, FlexibleContexts, NoMonomorphismRestriction, RankNTypes, ScopedTypeVariables, TypeOperators #-}
{- Synthesis of cache protocols from KBPs.
 - Copyright   :  (C)opyright 2011, 2012 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)

Grossly simplified.

-}
module Main where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude hiding ( (.), id )
import qualified Data.Map as Map

import ADHOC

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
--
-- If the effects happen in the same instant, then the kTests break:
-- we're updating memory depending on what we know about the value of
-- memory. So we need to delay the change to the mem_reg_valP probe to
-- the instant after the caches update memory.
--
memory :: (EC (~>), ArrowProbe (~>) (B (~>)))
       => (Signal, Signal, Signal, Signal) -> E (~>) () ()
memory (cache_owner, mem_read, mem_write, mem_val) =
  probeSigE cache_ownerP cache_owner >>>  probeSigE mem_readP mem_read >>> probeSigE mem_writeP mem_write >>> probeSigE mem_valP mem_val >>> (
  register_delayedE mem_reg_valP $ \(reg_set, reg_reset, reg_val) ->
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

proc_readP, proc_writeP, proc_valP, proc_cofP :: Integer -> ProbeID
proc_readP i = "pr" ++ show i
proc_writeP i = "pw" ++ show i
proc_valP i = "pv" ++ show i
proc_cofP i = "pcof" ++ show i

processor :: (EC (~>), ArrowProbe (~>) (B (~>)))
          => Integer -> (Signal, Signal, Signal, Signal) -> E (~>) () ()
processor i (proc_read, proc_write, proc_val, proc_cache_op_finished) =
      probeSigE (proc_readP i) proc_read >>> probeSigE (proc_writeP i) proc_write
  >>> probeSigE (proc_valP i) proc_val >>> probeSigE (proc_cofP i) proc_cache_op_finished
  >>> (loopE_ $ \exn -> emitE proc_write >>> whenE proc_cache_op_finished (throwE exn) >>> pauseE)

-------------------------------------------------------------------

-- Caches

c_knowsP, cline_valueP :: Integer -> ProbeID
c_knowsP i = "ck" ++ show i
cline_valueP i = "cval" ++ show i
cline_dirtyP i = "cdirty" ++ show i

cset i = "cs" ++ show i
creset i = "cr" ++ show i

kt i = "kt" ++ show i

-- | Cache @i@ knows the bit in memory, or the bit in the dirty cache
-- if there is one.
owner_val i = cache i `knows` neg (probe mem_reg_valP)

-- | Does this cache know the value of the cache line?
cache_knows i cache_does_know cache_val_set cache_val_reset =
      probeSigE (c_knowsP i) cache_does_know
  >>> ifE (kTest (owner_val i) >>> probeA (kt i)) (emitE cache_does_know >>> emitE cache_val_reset) (emitE cache_val_set)

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
            [ -- Write through on the first write, local operation thereafter.
              sigE proc_write
                :- (busOp busArb (
                            emitE mem_read >>> pauseE -- Indicate we want to read.
                        >>> pauseE -- Wait for a response from memory or another cache.
                        >>> emitE dirty -- FIXME timing: this cache is dirty in the next instant.
                        >>> emitE mem_write >>> whenE proc_val (emitE mem_val)) )
                   >>> presentE proc_val (emitE cache_val_set) (emitE cache_val_reset)
                   >>> emitE proc_cache_op_finished
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

Just (_, m, _) = broadcastSprSynthII' MinBisim system
ctlM = mkCTLModel m

-------------------------------------------------------------------
-- Specifications
-------------------------------------------------------------------

specs :: (Boolean b, Eq b) => [Spec b]
specs =
  [ sOK "memory is always F" $ ag (neg (probe mem_valP))
  -- , sOK "clines always F" $ ag (conjoin [ neg (probe (cline_valueP i)) | i <- caches ])
  , sOK "the caches always know the cache line" $ ag (conjoin [ probe (c_knowsP i) | i <- caches ])
  ]

test_specs = dynamicReordering ReorderStableWindow3 >> mcce ctlM specs
