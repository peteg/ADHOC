{-# LANGUAGE Arrows, FlexibleContexts, NoMonomorphismRestriction, RankNTypes, ScopedTypeVariables, TypeOperators #-}
{- Synthesis of cache protocols from KBPs.
 - Copyright   :  (C)opyright 2011, 2012 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -
 - This model satisfies "independent initialisation".
 -
 - A more realistic write-once cache. Flushing is still problematic.
 -
 - We optimise for bus operations here, not the amount of state the cache
 - controller has to maintain per cache line.
 -
 - FIXME
 - we could replace the processors with smaller FSMs written in ADHOC - should reduce the state by ~ 4 * 2 bits.
 -}
module Main ( main ) where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude hiding ( (.), id )

import ADHOC
import ADHOC.NonDet

import ADHOC.Control.Kesterel hiding ( SigAlt(..), sig_caseE )

import ADHOC.Knowledge

import ADHOC.ModelChecker.CTL as CTL
import ADHOC.ModelChecker.CounterExamples
import ADHOC.ModelChecker.Knowledge

import Broadcast

-- | A @case@ construct on signals.
data SigAlt (~>) env = Signal :- E (~>) env ()
infix 0 :-

sigCaseE :: EC (~>) => [SigAlt (~>) env] -> E (~>) env ()
sigCaseE alts = foldr (\(sig :- cmd) cmds -> presentE sig cmd cmds) nothingE alts

-------------------------------------------------------------------
-- Scenario
-------------------------------------------------------------------

caid :: Integer -> AgentID
caid i = "cache" ++ show i

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
-- FIXME the initial memory register value should perhaps be non-det.
--
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
  register_delayedE mem_reg_valP $ \(reg_set, reg_reset, reg_val) ->
  loopE (sigCaseE
      [ mem_read
          :-     pauseE -- "read"
             >>> presentE cache_owner
                   (presentE mem_val (emitE reg_set) (emitE reg_reset)) -- Cache claims ownership, record what it says
                   (whenE reg_val (emitE mem_val)) -- Caches silent, emit our value
      , mem_write :- presentE mem_val (emitE reg_set) (emitE reg_reset)
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

proc_readP, proc_writeP, procValP, proc_cofP :: Integer -> ProbeID
proc_readP i = "pr" ++ show i
proc_writeP i = "pw" ++ show i
procValP i = "pv" ++ show i
proc_cofP i = "pcof" ++ show i

processor :: (EC (~>), ArrowNonDet (~>) (B (~>)), ArrowProbe (~>) (B (~>)))
          => Integer -> (Signal, Signal, Signal, Signal) -> E (~>) () ()
processor i (proc_read, proc_write, proc_val, proc_cont) =
      probeSigE (proc_readP i) proc_read >>> probeSigE (proc_writeP i) proc_write
  >>> probeSigE (procValP i) proc_val >>> probeSigE (proc_cofP i) proc_cont
  >>> loopE (procOp >>> pauseE)
  where
    nondetEL = foldr1 nondetE
    cacheOp op = loopE_ (\exn -> op >>> whenE proc_cont (throwE exn) >>> pauseE)
    procOp = nondetEL
      [ -- Local operation
        nothingE
      , -- Memory operation: read
        cacheOp (emitE proc_read)
      , -- Memory operation: write 0.
        cacheOp (emitE proc_write)
      , -- Memory operation: write 1.
        cacheOp (emitE proc_write >>> emitE proc_val)
      ]

-------------------------------------------------------------------

-- Caches

cKnowsP, cValP, cDirtyP :: Integer -> ProbeID
cKnowsP i = "ck" ++ show i
cValP i = "cval" ++ show i
cDirtyP i = "cdirty" ++ show i

-- | Cache @i@ knows the bit in memory, or the bit in the dirty cache
-- if there is one.
owner_val :: Integer -> (KF -> KF) -> KF
owner_val i pol = caid i `knows`
  (   conjoin [ probe (cDirtyP j) --> pol (probe (cValP j)) | j <- caches ]
  /\ (conjoin [ neg (probe (cDirtyP j)) | j <- caches ] --> pol (probe mem_reg_valP)) )

kFIXME :: (EC (~>), ArrowKTest (~>), ArrowProbe (~>) (B (~>))) => Integer -> () ~> ()
kFIXME i = if i /= 1 then id else (
    kTest ( (map caid caches) `cknows_hat` mem_reg_valP) >>> probeA "cknows mem_reg_val" -- FIXME abstract probe name
    >>> arr (const ()) )

-- | Does this cache know the value of the cache line?
cKnows i cache_knows cache_knowsVal =
      probeSigE (cKnowsP i) cache_knows
--  >>> lift (kFIXME i)
  >>> kTestE (owner_val i neg)
        (emitE cache_knows)
        (kTestE (owner_val i id)
           (emitE cache_knows >>> emitE cache_knowsVal)
           nothingE)

-- | Respond to a memory read request if we're dirty.
--
-- This cleans the cache.
--
-- We use the condition @isDirty@ rather than @cache_knows@ as
-- the cache may know the cache line but not be the owner.
cOwner cache_owner mem_read mem_val cLine clean isDirty =
    whenE mem_read
      (whenE isDirty
         (emitE cache_owner
      >>> whenE cLine (emitE mem_val)
      >>> emitE clean)) -- Clean in the next instant.

-- | Unconditional bus operation: wait for the bus and then execute
-- @op@.
busOp (req, ack) op =
  sustainWhileE req $
    loopE_ (\exn -> whenE ack (throwE exn) >>> pauseE) >>> op

-- | Guarded bus operation: wait for the bus, and if @cond@ becomes
-- true before we acquire the bus then do nothing, otherwise execute
-- @op@.
guardedBusOp (req, ack) cond op =
  sustainWhileE req $
    loopE_ $ \exn -> presentE cond
                        (throwE exn)
                        (whenE ack (op >>> throwE exn))
                      >>> pauseE

cache i -- cache number
  (cache_owner, mem_read, mem_write, mem_val) -- bus signals
  busArb -- bus arbitration
  (proc_read, proc_write, proc_val, proc_cont) -- processor signals
  = registerE (cValP i) $ \(cLine_set, cLine_reset, cLine) ->
    register_delayedE (cDirtyP i) $ \(dirty, clean, isDirty) ->
    signalE $ \(cache_knows, cache_knowsVal) ->
        each_instantE [ cKnows i cache_knows cache_knowsVal
                      , cOwner cache_owner mem_read mem_val cLine clean isDirty ]
      ||||
        -- Processor request.
        loopE (sigCaseE
            [ -- Read
              proc_read
                :- unlessE cache_knows -- otherwise Read hit (local)
                     (guardedBusOp busArb cache_knows (
                            emitE mem_read >>> pauseE -- Indicate we want to read.
                        >>> pauseE)) -- Wait for a response from memory or another cache.
                   >>> whenE cache_knowsVal (emitE proc_val) -- The kTest takes care of the response.
                   >>> emitE proc_cont
              -- Write through on the first write, local operation thereafter.
            , proc_write
                :- unlessE isDirty -- otherwise Write hit (local)
                     -- Write miss (bus)
                     (busOp busArb (
                            emitE mem_read >>> pauseE -- Indicate we want to read.
                        >>> pauseE -- Wait for a response from memory or another cache.
                        >>> emitE dirty -- FIXME timing: this cache is dirty in the next instant.
                        >>> emitE mem_write >>> whenE proc_val (emitE mem_val))
                     )
                   >>> presentE proc_val (emitE cLine_set) (emitE cLine_reset)
                   >>> emitE proc_cont
              -- No activity from the processor.
              -- In a more complete model we'd do a flush here.
            ] >>> pauseE )

-------------------------------------------------------------------

-- Composition.

proc_cache i busSigs busArb = signalE $ \procSigs ->
    processor i procSigs
  ||||
    cache i busSigs busArb procSigs

system = arbitratedBus procs
  where
    probes (cache_owner, mem_read, mem_write, mem_val) =
            probeSigE cache_ownerP cache_owner >>> probeSigE mem_readP mem_read
        >>> probeSigE mem_writeP mem_write >>> probeSigE mem_valP mem_val

    procs busSigs = ( probes busSigs
                    , (mkSizedListf $ \i -> (caid i, proc_cache i busSigs)) `withLength` (undefined :: Caches)
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

specs :: [Spec BDD]
specs =
  [
    -- Basic sanity.
    sOK "dirtiness is always possible" $ ag (conjoin [ ef (probe (cDirtyP i)) | i <- caches ])
  , sOK "dirtiness is exclusive" $ ag (conjoin
      [ probe (cDirtyP i) --> conjoin [ neg (probe (cDirtyP j))
                                           | j <- caches, j /= i ]
      | i <- caches ])
  , sOK "procs can infinitely often read" $ ag (conjoin [ ef (probe (proc_readP i)) | i <- caches ])
  , sOK "procs can infinitely often write" $ ag (conjoin [ ef (probe (proc_writeP i)) | i <- caches ])
  , sOK "cache vals can become 0" $ ag (conjoin [ ef (neg (probe (cValP i))) | i <- caches ])
  , sOK "cache vals can become 1" $ ag (conjoin [ ef      (probe (cValP i))  | i <- caches ])
  , sOK "mem_reg can always become 0" $ ag (ef (neg (probe mem_reg_valP)))
  , sOK "mem_reg can always become 1" $ ag (ef      (probe mem_reg_valP))
  , sFail "there are no bus read actions" $ ag (neg (probe mem_readP))
  , sOK "the bus can always be idle in the future" $ ag (ef (neg (probe mem_writeP) /\ neg (probe mem_readP)))
  , sOK "always possible for a bus write to occur in the future (0)" $ ag (ef (probe mem_writeP /\      probe mem_valP))
  , sOK "always possible for a bus write to occur in the future (1)" $ ag (ef (probe mem_writeP /\ neg (probe mem_valP)))
  , sOK "both processors can simulataneously do local computation" $
       ag (ef (conjoin [ neg (probe (proc_readP i)) /\ neg (probe (proc_writeP i))
                       | i <- caches ]))
  , sFail "the bus is infinitely often active (fails without proc fairness)" $ ag (af (probe mem_writeP \/ probe mem_readP))
  , sOK "cache owner implies a cache is dirty" $
       -- Messy: the cache /was/ dirty in the previous instant.
       -- ag (probe cache_ownerP --> disjoin [ probe (cDirtyP i) | i <- caches ])
       ag (conjoin [ neg (probe (cDirtyP i)) | i <- caches ] --> ax (neg (probe cache_ownerP)))
  , sFail "processor writes 1 eventually bus sees a write of 1" $
       -- Fails due to local writes (dirtiness)
       ag (conjoin [ (probe (proc_writeP i) /\ probe (procValP i))
                        --> af (probe mem_writeP /\ probe mem_valP)
                   | i <- caches ])
  , sOK "cache-local writes are possible" $
      ag (conjoin [ ef (probe (proc_writeP i) /\ probe (proc_cofP i) /\ ex (probe (proc_writeP i) /\ probe (proc_cofP i)))
                  | i <- caches ])
  , sOK "the processors can complete an operation at the same time" $
      ag ( ef ( conjoin [ probe (proc_cofP i) | i <- caches ] ))
  , sOK "once a processor completes a write, all reads and writes are local until a bus read" $
      ag (conjoin [ (probe (proc_writeP i) /\ probe (proc_cofP i))
                      --> ( ( (probe (proc_writeP i) \/ probe (proc_readP i)) --> probe (proc_cofP i) )
                              `au_unbounded` probe mem_readP )
                  | i <- caches ])

    -- Basic epistemic sanity.
  , sFail "the caches always know the cache line" $ ag (conjoin [ probe (cKnowsP i) | i <- caches ])
  , sOK "if a clean cache knows the cache line, they all do" $
      ag (conjoin [ (neg (probe (cDirtyP i)) /\ probe (cKnowsP i))
                    --> conjoin [ probe (cKnowsP j) | j <- caches ]
                  | i <- caches ])
  , sOK "dirtiness implies knowledge" $ ag (conjoin [ probe (cDirtyP i) --> probe (cKnowsP i) | i <- caches ])
  , sOK "whenever a cache completes an operation, it knows the value of the cache line" $
      ag ( conjoin [ probe (proc_cofP i) --> probe (cKnowsP i)
                   | i <- caches ])
      -- Checking CK slows things down in a big way.
--  , sOK "the memory register value is common (SPR) knowledge" $ ag (probe "cknows mem_reg_val")

    -- Coherence.
  , sOK "cache coherence (1)" $
      ag (conjoin [ (probe (proc_writeP i) /\ probe (procValP i) /\ probe (proc_cofP i))
                      --> ax ( (conjoin [ (probe (proc_readP j) /\ probe (proc_cofP j)) --> probe (procValP j)
                                        | j <- caches ])
                                 `au_unbounded`
                                    (disjoin [ probe (proc_writeP j) /\ neg (probe (procValP j)) /\ probe (proc_cofP j)
                                             | j <- caches ]) )
                  | i <- caches ])
  , sOK "cache coherence (0)" $
      ag (conjoin [ (probe (proc_writeP i) /\ neg (probe (procValP i)) /\ probe (proc_cofP i))
                      --> ax ( (conjoin [ (probe (proc_readP j) /\ probe (proc_cofP j)) --> neg (probe (procValP j))
                                        | j <- caches ])
                                 `au_unbounded`
                                    (disjoin [ probe (proc_writeP j) /\ probe (procValP j) /\ probe (proc_cofP j)
                                             | j <- caches ]) )
                  | i <- caches ])
  ]

-------------------------------------------------------------------

{-

The model seems to benefit from reordering. Not so sure about the
property checking.

Crash when using ReorderNone:

#0  0x00ebe7c9 in Cudd_Ref ()
#1  0x003ac2c8 in cudd_bddSwapVariables ()
#2  0x003937b3 in s5zM_info ()

Possibly we have (partially?) unevaluated BDD operations and switching
off reordering confuses them. Check the CUDD manual for what gets
broken by reordering.

-}

main :: IO ()
main =
  do dynamicReordering ReorderStableWindow3 -- ReorderSiftSym -- ReorderSift
     -- unstableTrace system
     m `seq` putStrLn "System is constructive!"
     -- unstableTrace system
     bddPrintInfo
     m `seq` putStrLn "Synthesis completed!"
     -- dot kautos
     -- dynamicReordering ReorderNone -- FIXME causes CUDD to crash with a bus error, see above.
     putStrLn $ "Checking properties..."
     _ <- mcce ctlM specs
     return ()
