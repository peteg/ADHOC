{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{- Kesterel top-level packaging.
 - Copyright   :  (C)opyright 2006, 2009-2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -
 - Cementing the type signatures here, when the implementations are
 - rapidly changing, is unwise.
 -
 - The primed variants use the boolean type from the underlying Arrow.
 -}
module ADHOC.Control.Kesterel
    (
      -- * Kernel Esterel
      E, EC
    , (||||), parE
    , runE, runE'

    , nothingE
    , ifE, ifE'
    , loopE
    , pauseE, probePauseE

    , probeE
    , probeSigE
    , activeE

    , Signal
    , signalE
    , sigE
    , emitE
    , presentE
    , abortE, abortE'

    , Exception
    , catchE
    , throwE

      -- * Non-determinism
    , nondetE
    , nondetFairE

      -- * Interface with circuits
    , bool2sig

      -- * Knowledge operators
    , agentE
    , kTestE

      -- * Extra primitives
    , sustainWhileE

      -- * Derived combinators
    , awaitE
    , await_immediateE, await_immediateE'
    , haltE
    , loopE_
    , loop_eachE, loop_eachE'
    , every_immediateE, every_immediateE'
    , sustainE
    , unlessE
    , whenE
    , SigAlt(..), sig_caseE
    , weak_abortE
    , each_instantE
    ) where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude ()
import ADHOC.Circuits
import ADHOC.NonDet

import ADHOC.Optimise	( runOpt )
import ADHOC.Control.Kesterel.Kernel

----------------------------------------
-- Circuit interface.
----------------------------------------

-- | Compile an 'E' into an optimised circuit.
runE = runOpt . runE'

-- FIXME not the most convenient thing to use: not a command combinator ??
-- FIXME generic this too??
bool2sig :: EC (~>)
         => (Signal -> E (~>) env d)
         -> E (~>) (env, B (~>)) d
bool2sig f =
  signalE $ \s ->
    proc (env, x) ->
      do (| ifE (returnA -< x)
              (emitE s -< ())
              (nothingE -< ()) |)
         f s -< env

----------------------------------------
-- 'loopE' variants.
----------------------------------------

-- | Create an exception for later exiting the loop. FIXME
loopE_ :: EC (~>)
       => (Exception -> E (~>) env b)
       -> E (~>) env b
loopE_ body = catchE (loopE . body)

-- | Primer, p61: "Execute @p@ right away, and restart it afresh
-- whenever the delay elapses [signal s is present]."
loop_eachE s p = loopE ((p >>> haltE) `abortE` s)

loop_eachE' s p = loopE (abortE' s (p >>> haltE))

every_immediateE s p = proc env ->
  do await_immediateE s -< ()
     loop_eachE s p -< env

every_immediateE' s p = proc env ->
  do await_immediateE' s -< env
     loop_eachE' s p -< env

----------------------------------------
-- The "await" combinators.
----------------------------------------

-- | Wait an instant, and then for each succeeding instant pause if
-- the signal is absent.
awaitE s = pauseE >>> await_immediateE s

-- | If the signal is present, pass control to the next statement,
-- otherwise pause and repeat. FIXME verify, p61.
--
-- FIXME loop safety??
await_immediateE s = loopE_ $ \e ->
  (presentE s (throwE e) nothingE) >>> pauseE

await_immediateE' s = s >>> loopE_ (\e -> proc b ->
  do (| ifE (returnA -< b) (throwE e -< ()) (nothingE -< ()) |)
     pauseE -< ())

-------------------------------------------------------------------
-- Miscellaneous combinators.
-------------------------------------------------------------------

-- | Halt for all time. The output tracks the input at each instant
-- (i.e. it does not sample-and-hold).
haltE = loopE pauseE

-- | Continually emit a signal.
sustainE s = loopE (emitE s >>> pauseE)

-- | Do 'f' unless a signal is present (cf 'unless').
unlessE s f = presentE s nothingE f

-- | Do 'f' unless a signal is absent (cf 'when').
whenE s f = presentE s f nothingE

-- | \"Fairly\" non-deterministically choose between two 'E'
-- computations.
--
-- FIXME introduces unnecessary branching, see Kernel / nondetE.
nondetFairE = ifE nondetFairBitA

-- | A @case@ construct on signals.
data SigAlt (~>) env = E (~>) env (B (~>)) :- E (~>) env ()

infix 0 :-

sig_caseE :: EC (~>) => [SigAlt (~>) env] -> E (~>) env ()
sig_caseE alts = foldr (\(sig :- cmd) cmds -> ifE' sig cmd cmds) nothingE alts

-- | Weak abortion: @p@ receives control in the instant that @s@ is
-- present. The test for @s@ happens after one instant. FIXME
-- weak_abortE :: EC (~>) => E (~>) b () -> Signal -> E (~>) b ()
-- weak_abortE p s = catchE $ \e ->
--   (p >>> throwE e) |||| (loopE (pauseE >>> presentE s (throwE e) nothingE))
weak_abortE p s = catchE $ \e ->
  (p >>> throwE e) |||| (pauseE >>> loopE (presentE s (throwE e) nothingE >>> pauseE))

-- | Sequence a list of statements with @(>>>)@ and append @>>>
-- pauseE@ to it.
each_instantE :: EC (~>) => [E (~>) b b] -> E (~>) b ()
each_instantE = loopE . foldr (>>>) pauseE
