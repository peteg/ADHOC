{-# LANGUAGE BangPatterns, GADTs, TypeFamilies #-}
{- The guts of the arrowized Esterel circuit translation.
 - Copyright   :  (C)opyright 2006, 2009-2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -
 - The 'E' arrow acts as an /environment transformer/.
 -
 - Sketch following Berry, CONSTRUCTIVE SEMANTICS OF ESTEREL.
 -
 - Invariants:
 -  completion codes are one-hot p113.

FIXME lint all the signatures.

FIXME ifE etc: intuitively this represents control flow choice. Data
should depend on signals, not control flow. Make this clear. For this
reason we don't allow ifE etc. to return data.

FIXME we don't try to treat schizophrenia here: we just want something
that plays nicely with our circuit combinators (probes and
kTests). Berry's full circuit translation duplicates things in
inconvenient ways; we could make it work, but it's too much hassle.

FIXME verify: According to Berry Ch12, the constructivity checker will
reject some "constructive" Esterel programs. These get compiled to
non-constructive circuits, and the schizophrenia machinery would
duplicate logic to make it all work.

This is probably what Lusterel is trying to fix.

Completion codes:

K0 -> terminated
K1 -> paused
Kn, n > 1 -> exception

FIXME:
 - local signals are totally unsafe presently.
 - one case where a static/dynamic split would be useful.

Observe that we cannot chain the environments through in the obvious
way: each leaf command has to determine the signal and exception
signals, for otherwise the ultimate combinational loop is underdefined
- it will be undefined if the signal is not emitted.

According to Berry this translation is "partially correct" -- I think this
means that if this translation miscompiles an Esterel program according to
his semantics then the resulting circuit is non-constructive.

Idiomatically everywhere Berry uses signals we want to use circuits,
and then provide a signal-to-circuit Arrow.

FIXME play the Optimise game at the Kesterel level? We certainly can
remove some trivial structural things, e.g. x |||| nothingE --> x.

-}
module ADHOC.Control.Kesterel.Kernel where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude ()

import ADHOC.Circuits hiding ( rem, sin )
import ADHOC.Generics
import ADHOC.Model ( KF, ArrowAgent(..), ArrowKTest(..), ArrowProbe(..),
                     RenderInState(..) )
import ADHOC.NonDet -- FIXME ( ArrowUnsafeNonDet(..) )

import Data.Sequence ( Seq, (|>), (><), ViewR(..) )
import qualified Data.Sequence as Seq
import qualified Data.Foldable as F

import ADHOC.Constructivity ( CArrow )
import ADHOC.NetList ( NLArrow )

-------------------------------------------------------------------
-- Cheap and cheerful Environment/Reader monad.
-------------------------------------------------------------------

-- | Environment/Reader functor/monad.
newtype EnvM s a = EnvM { runEnvM :: s -> a }

instance Functor (EnvM s) where
    fmap f (EnvM g) = EnvM (g >>> f)

instance Monad (EnvM s) where
    return = EnvM . const
    f >>= g = EnvM (\s -> runEnvM (g (runEnvM f s)) s)

readEnvM :: EnvM s s
readEnvM = EnvM id

inEnvEM :: s -> EnvM s a -> EnvM s a
inEnvEM s f = EnvM $ const (runEnvM f s)

-------------------------------------------------------------------
-- Extra Sequence combinators.
-------------------------------------------------------------------

-- | Combinational loop over a vector of signals.
combLoopF :: ArrowCombLoop (~>) r
          => Int
          -> (b, Seq r) ~> (c, Seq r)
          -> b ~> c
combLoopF k0 f = arr (\b -> (b, Seq.empty)) >>> cl k0 >>> arr fst
  where
    cl 0 = f
    cl k = proc (b, xs) ->
      (| combLoop (\x ->
           do ~(c, d) <- cl (k - 1) -< (b, xs |> x)
              let (xs' :> x') = Seq.viewr d
              returnA -< ((c, xs'), x')) |)

lift2 :: Arrow (~>)
      => Int
      -> ((c, d) ~> e)
      -> (Seq c, Seq d) ~> Seq e
lift2 k0 f = opL k0
  where
    opL 0 = arr (const Seq.empty)
    opL k = proc (xs, ys) ->
      do let !(xs' :> x') = Seq.viewr xs
             !(ys' :> y') = Seq.viewr ys
         (| (liftA2 (|>)) (opL (k - 1) -< (xs', ys')) (f -< (x', y')) |)

-- FIXME verify: process the sequence right-to-left.
rowA :: Arrow (~>)
     => Int
     -> ((a, b) ~> (a, c))
     -> (a, Seq b) ~> (a, Seq c)
rowA k0 f = opL k0
  where
    opL 0 = arr (\(a, _) -> (a, Seq.empty))
    opL k = proc (a, xs) ->
      do let !(xs' :> x') = Seq.viewr xs
         (a', c)   <- f -< (a, x')
         (a'', cs) <- opL (k - 1) -< (a', xs')
         returnA -< (a'', cs |> c)

-------------------------------------------------------------------
-- Esterel translation boilerplate.
-------------------------------------------------------------------

-- | We need to track some static information: signal and exception
-- scopes.
data Static
    = Static
      { exnID :: !Int
      , sigID :: !Int
      } deriving Show

-- | The dynamic environment: the values of signals.
newtype Esigs b = Esigs { eSigs :: Seq b }
                deriving Show

instance StructureDest b b => StructureDest b (Esigs b) where
  destructure = F.toList . eSigs

instance RenderInState b b' => RenderInState (Esigs b) b' where
    renderInState = mconcat . map renderInState . F.toList . eSigs

cenv_exns_empty :: Static -> b -> (Esigs b, Seq b)
cenv_exns_empty s ff =
  ( Esigs{eSigs = Seq.replicate (sigID s) ff}
  , Seq.replicate (exnID s) ff )

-- | Dynamic control inputs for 'E' sub-circuits.
data Cin b
    = Cin
      { ciGo :: b
      , ciRes :: b
      , ciSusp :: b
      , ciKill :: b
      } deriving Show

instance StructureDest b b => StructureDest b (Cin b) where
  destructure = \(Cin a b c d) -> [a,b,c,d]

instance RenderInState b b' => RenderInState (Cin b) b' where
    renderInState (Cin g r s k) = mconcat (map renderInState [g, r, s, k])

-- | Dynamic control outputs for 'E' sub-circuits. Mandatory: 'coSelected', 'coTerminated'.
data Cout b
    = Cout
      { coSelected :: b -- ^ Selected (an enclosed 'pause' is paused)
      , coTerminated :: b
      , coPaused :: b
      , coExns :: Seq b
      } deriving Show


-- | The dynamic part of the @E@ arrow: map control and data inputs
-- into control and data outputs.
type Dynamic (~>) c d =
  (Cin (B (~>)), Esigs (B (~>)), c) ~> (Cout (B (~>)), Esigs (B (~>)), d)

-- | The @E@ arrow.
newtype E (~>) c d = E { unE :: EnvM Static (Dynamic (~>) c d) }

-- | A typical Esterel program needs these classes.
class (ArrowLoop (~>), ArrowDelay (~>) (B (~>)), ArrowCombLoop (~>) (B (~>)),
       ArrowComb (~>), ArrowInit (~>))
    => EC (~>)

instance EC CArrow
instance EC (NLArrow detail)

-- | Lift up computations in the underlying arrow.
instance EC (~>) => ArrowTransformer (E) (~>) where
  lift = liftE

instance EC (~>) => Category (E (~>)) where
  id = lift id
  f . g = seqE g f

-- FIXME first can be implemented much more efficiently
instance EC (~>) => Arrow (E (~>)) where
  arr = lift . arr
  first f = f *** id
  (***) = seqE_par_env

instance EC (~>) => ArrowLoop (E (~>)) where
  loop = arrowLoopE

-- Lift circuits in the obvious way. Handy for boolean combinations of
-- signals.
instance EC (~>) => ArrowComb (E (~>)) where
  -- The type of a single rail.
  type B (E (~>)) = B (~>)

  falseA = lift falseA
  trueA  = lift trueA

  andA = lift andA
  notA = lift notA
  nandA = lift nandA
  orA  = lift orA
  xorA = lift xorA
  iffA = lift iffA
  impA = lift impA

-------------------------------------------------------------------
-- Lifting and looping.
-------------------------------------------------------------------

-- | Lift an underlying arrow /f/, which is executed at every instant.
liftE :: forall (~>) b c. EC (~>) => (b ~> c) -> E (~>) b c
liftE f = E $
  do s <- readEnvM
     return $ proc (cin, _ienv, c) ->
       do d <- f -< c
          ff <- falseA -< ()
          let (oenv, exns) = cenv_exns_empty s ff
          returnA -< ( Cout { coSelected = ff
                            , coTerminated = ciGo cin
                            , coPaused = ff
                            , coExns = exns }
                     , oenv
                     , d)

-- | Does nothing, consumes no time.
nothingE :: EC (~>) => E (~>) env ()
nothingE = arr (const ())

-- | Data recursion: hoist up an underlying instance of
-- 'ArrowLoop'. Otherwise oblivious to the 'E' shenanigans.
arrowLoopE :: EC (~>) => E (~>) (b, d) (c, d) -> E (~>) b c
arrowLoopE (E fE) = E $
  do f <- fE
     return $ proc (cin, ienv, b) ->
       do rec ~(cout, f_env, ~(c, d)) <- f -< (cin, ienv, (b, d))
          returnA -< (cout, f_env, c)

-------------------------------------------------------------------
-- Kernel Esterel
-------------------------------------------------------------------

-- | Rest here for an instant.
pauseE_prim :: forall (~>) env. EC (~>) => (B (~>) ~> B (~>)) -> E (~>) env ()
pauseE_prim pA = E $
  do s <- readEnvM
     return $ note "pauseE" $ proc (cin, _ienv, _c) ->
       do nKill <- notA -< ciKill cin
          rec reg <- (| delayAC (falseA -< ()) (andA -< (t, nKill)) |)
              t <- orA <<< second andA -< (ciGo cin, (ciSusp cin, reg))
          pA -< reg
          terminated <- andA -< (reg, ciRes cin)
          ff <- falseA -< ()
          let (oenv, exns) = cenv_exns_empty s ff
          returnA -< ( Cout { coSelected = reg
                            , coTerminated = terminated
                            , coPaused = ciGo cin
                            , coExns = exns }
                     , oenv
                     , () )

pauseE :: EC (~>) => E (~>) env ()
pauseE = pauseE_prim id

probePauseE :: (EC (~>), ArrowProbe (~>) (B (~>)))
            => ProbeID -> E (~>) env ()
probePauseE = pauseE_prim . probeA

-- | Infinitely loop.
-- FIXME not correct for unsafe loops?
-- This definitely requires 'ArrowCombLoop': see Berry p131.
loopE :: EC (~>)
      => E (~>) env b
      -> E (~>) env b
loopE (E fE) = E $
  do f <- fE
     return $ note "loopE" $ proc (cin, ienv, c) ->
       (| combLoop (\terminated ->
            do f_go <- orA -< (ciGo cin, terminated)
               (f_cout, f_env, d) <- f -< (cin{ciGo = f_go}, ienv, c)
               ff <- falseA -< ()
               returnA -< ( (f_cout{coTerminated = ff}, f_env, d)
                          , coTerminated f_cout ) ) |)

-- | Sequential composition of two 'E' computations, chaining the data
-- output of the first into the second.
seqE :: forall (~>) b c d.
        ArrowComb (~>)
     => E (~>) b c -> E (~>) c d -> E (~>) b d
(E fE) `seqE` (E gE) = E $
  do f <- fE
     g <- gE
     s <- readEnvM
     return $ {- note "seqE" $ -} proc (cin, ienv, c) ->
       do (f_cout, f_env, d) <- f -< (cin, ienv, c)
          (g_cout, g_env, e) <- g -< (cin{ciGo = coTerminated f_cout}, ienv, d)
          oenv <- combine_envs s -< (f_env, g_env)
          cout <- combine_seq_couts s -< (f_cout, g_cout)
          returnA -< (cout, oenv, e)

-- | Sequential composition of two 'E' computations, splitting the
-- data between the two. For @(***)@.
seqE_par_env :: forall (~>) env env' b b'.
                ArrowComb (~>)
             => E (~>) env b
             -> E (~>) env' b'
             -> E (~>) (env, env') (b, b')
(E fE) `seqE_par_env` (E gE) = E $
  do f <- fE
     g <- gE
     s <- readEnvM
     return $ {- note "seqE" $ -} proc (cin, ienv, (c, c')) ->
       do (f_cout, f_env, d ) <- f -< (cin, ienv, c)
          (g_cout, g_env, d') <- g -< (cin{ciGo = coTerminated f_cout}, ienv, c')
          oenv <- combine_envs s -< (f_env, g_env)
          cout <- combine_seq_couts s -< (f_cout, g_cout)
          returnA -< (cout, oenv, (d, d'))

combine_envs :: forall (~>). (ArrowComb (~>))
             => Static -> (Esigs (B (~>)), Esigs (B (~>))) ~> Esigs (B (~>))
combine_envs s = proc (f_env, g_env) ->
  do sigs' <- lift2 (sigID s) orA -< (eSigs f_env, eSigs g_env)
     returnA -< Esigs{eSigs = sigs'}

combine_seq_couts :: ArrowComb (~>)
                  => Static -> (Cout (B (~>)), Cout (B (~>))) ~> Cout (B (~>))
combine_seq_couts s = proc (f_cout, g_cout) ->
  do selected <- orA -< (coSelected f_cout, coSelected g_cout)
     let terminated = coTerminated g_cout
     paused <- orA -< (coPaused f_cout, coPaused g_cout)
     exns <- lift2 (exnID s) orA -< (coExns f_cout, coExns g_cout)
     returnA -< Cout { coSelected = selected
                     , coTerminated = terminated
                     , coPaused = paused
                     , coExns = exns }

-------------------------------------------------------------------
-- Parallel composition.
-------------------------------------------------------------------

infixr 2 ||||

(||||) :: EC (~>) => E (~>) env () -> E (~>) env () -> E (~>) env ()
f |||| g  = f `parE` g >>> arr (const ())

-- | Parallel composition. Think of this as "control-parallelism", not
-- the "data-parallelism" provided by 'seqE_par_env'.
parE :: forall (~>) env b b'. EC (~>)
     => E (~>) env b -> E (~>) env b' -> E (~>) env (b, b')
(E fE) `parE` (E gE) = E $
  do f <- fE
     g <- gE
     s <- readEnvM
     return $ note "parE" $ proc (cin, ienv, c) ->
       do (f_cout, f_env, d ) <- f -< (cin, ienv, c)
          (g_cout, g_env, d') <- g -< (cin, ienv, c)
          selected <- orA -< (coSelected f_cout, coSelected g_cout)
          (terminated, paused, exns) <- synchronise s -< (cin, f_cout, g_cout)
          oenv <- combine_envs s -< (f_env, g_env)
          returnA -< ( Cout { coSelected = selected
                            , coTerminated = terminated
                            , coPaused = paused
                            , coExns = exns }
                     , oenv
                     , (d, d') )

-- | Synchronisation, following Berry p122: compute the completion
-- code of the two threads.
synchronise :: forall (~>).
               ArrowComb (~>)
            => Static
            -> (Cin (B (~>)), Cout (B (~>)), Cout (B (~>)))
            ~> (B (~>), B (~>), Seq (B (~>)))
synchronise s = note "synchronise" $ proc (cin, f_cout, g_cout) ->
  do lem <- notA <<< orA -< (coSelected f_cout, ciGo cin)
     rem <- notA <<< orA -< (coSelected g_cout, ciGo cin)
     ((l0, r0), terminated) <- max_completion_code -< ((lem, rem), (coTerminated f_cout, coTerminated g_cout))
     ((l1, r1), paused) <- max_completion_code -< ((l0, r0), (coPaused f_cout, coPaused g_cout))
     (_, exns') <- rowA (exnID s) max_completion_code -< ((l1, r1), Seq.zip (coExns f_cout) (coExns g_cout))
     returnA -< (terminated, paused, exns')

max_completion_code :: ArrowComb (~>)
                    => ((B (~>), B (~>)), (B (~>), B (~>))) ~> ((B (~>), B (~>)), B (~>))
max_completion_code = proc ((lprev, rprev), (lexn, rexn)) ->
  do lnext    <- orA -< (lprev, lexn)
     rnext    <- orA -< (rprev, rexn)
     exn_both <- orA -< (lexn, rexn)
     exn      <- andA <<< second andA -< (exn_both, (lnext, rnext))
     returnA -< ((lnext, rnext), exn)

-------------------------------------------------------------------
-- Local signals.
-------------------------------------------------------------------

-- | User-visible signals.
newtype Signal = Signal Int

instance StructureDest Signal Signal where
  destructure = (:[])

instance Structure Signal Signal where
  type SIwidth Signal Signal = One
  structure = sallocSM

-- | Allocate scoped local 'Signal's.
--
-- We don't need to worry about signal scopes here! If they get
-- Arrow-returned that's OK, there's no combinator @E (~>)
-- Signal b@.
signalE :: forall (~>) env b v.
           (EC (~>), Structure Signal v)
        => (v -> E (~>) env b)
        -> E (~>) env b
signalE fE = E $
  do s <- readEnvM
     let next_sid = sigID s + fromInteger width
         sids = [sigID s .. next_sid - 1]
         s' = s{sigID = next_sid}
         (v, xs) = runStateM structure (map Signal sids)
     f <- assert (null xs) $ inEnvEM s' (unE (fE v))
     return $ proc (cin, ienv, c) ->
       do (| (combLoopF (fromInteger width)) (\s_vals ->
               do (f_cout, f_env, d) <- f -< (cin, ienv{eSigs = eSigs ienv >< s_vals}, c)
                  let (penv, s_vals') = sigID s `Seq.splitAt` eSigs f_env
                      oenv = f_env{eSigs = penv}
                  returnA -<
                             -- trace ("ienv: " ++ show (Seq.length (eSigs ienv))
                             --     ++ " fenv: " ++ show (Seq.length (eSigs f_env))
                             --     ++ " s_vals: " ++ show (Seq.length s_vals)
                             --     ++ " s_vals': " ++ show (Seq.length s_vals')
                             --     ++ " oenv: " ++ show (Seq.length (eSigs oenv))) $
                             -- assert (Seq.length penv == Seq.length (eSigs ienv)) $
                             -- assert (Seq.length s_vals == fromInteger width) $
                             -- assert (Seq.length s_vals' == fromInteger width) $
                             -- assert (Seq.length (eSigs ienv) == Seq.length (eSigs oenv)) $
                             ((f_cout, oenv, d), s_vals') ) |)
  where
    width = c2num (undefined :: SIwidth Signal v) :: Integer

-- | Project a signal out of the Esterel environment.
sigE :: forall (~>) env.
        ArrowComb (~>)
     => Signal -> E (~>) env (B (~>))
sigE (Signal sid) = E $
  do s <- readEnvM
     return $ proc (cin, ienv, _c) ->
       do ff <- falseA -< ()
          let (oenv, exns') = cenv_exns_empty s ff
          returnA -< ( Cout { coSelected = ff
                            , coTerminated = ciGo cin
                            , coPaused = ff
                            , coExns = exns' }
                     , oenv
                     , eSigs ienv `Seq.index` sid )

-- | Emit a 'Signal'.
emitE :: forall (~>) env. EC (~>) => Signal -> E (~>) env ()
emitE (Signal sid) = E $
  do s <- readEnvM
     return $ proc (cin, _ienv, _c) ->
       do ff <- falseA -< ()
          let (oenv, exns) = cenv_exns_empty s ff
          returnA -< ( Cout { coSelected = ff
                            , coTerminated = ciGo cin
                            , coPaused = ff
                            , coExns = exns }
                     , oenv{eSigs = Seq.update sid (ciGo cin) (eSigs oenv)}
                     , () )

-- | Branch on an arbitrary test.
ifE :: forall (~>) env. EC (~>)
    => (env ~> B (~>))
    -> E (~>) env ()
    -> E (~>) env ()
    -> E (~>) env ()
ifE cond (E thenEM) (E elseEM) = E $
  do thenE <- thenEM
     elseE <- elseEM
     s <- readEnvM
     return $ note "ifE" $ proc (cin, ienv, c) ->
       do t <- cond -< c
          t_go <- andA -< (ciGo cin, t)
          e_go <- (returnA -< ciGo cin) `andAC` (notA -< t)
          (t_cout, t_env, _t_d) <- thenE -< (cin{ciGo = t_go}, ienv, c)
          (e_cout, e_env, _e_d) <- elseE -< (cin{ciGo = e_go}, ienv, c)
          oenv <- combine_envs s -< (t_env, e_env)
          exns' <- lift2 (exnID s) orA -< (coExns t_cout, coExns e_cout)
          selected <- orA -< (coSelected t_cout, coSelected e_cout)
          terminated <- orA -< (coTerminated t_cout, coTerminated e_cout)
          paused <- orA -< (coPaused t_cout, coPaused e_cout)
          returnA -< ( Cout { coSelected = selected
                            , coTerminated = terminated
                            , coPaused = paused
                            , coExns = exns' }
                     , oenv
                     , () )

-- | FIXME variant: test is in an Esterel context. The type is totally bizarre.
-- ifE' :: (ArrowComb (~>), ArrowMux (~>) d)
--      => E (~>) c (B (~>))
--      -> E (~>) c d
--      -> E (~>) c d
--      -> E (~>) c d
ifE' condE thenE elseE = proc c ->
  do cond <- condE -< c
     (| (ifE_perm thenE elseE) (returnA -< cond) |)
-- FIXME putting this in a where clause triggers a GHC 7.0.3 bug
ifE_perm thenE elseE i = ifE i thenE elseE

-- | Test for the presence of a signal.
presentE :: EC (~>)
         => Signal
         -> E (~>) c ()
         -> E (~>) c ()
         -> E (~>) c ()
presentE s thenE elseE = proc c ->
  do v <- sigE s -< c
     (| ifE (returnA -< v) (thenE -< c) (elseE -< c) |)

-- | Non-deterministcally choose between two "E" computations.
--
-- FIXME This formulation using "unsafeNonDetInstAC" leads to less
-- branching in the resulting automaton. Unfortunately it doesn't seem
-- to be correct.

-- nondetE :: forall (~>) env. (ArrowUnsafeNonDet (~>) (B (~>)), EC (~>))
--         => E (~>) env ()
--         -> E (~>) env ()
--         -> E (~>) env ()
nondetE = ifE nondetBitA
{-
nondetE (E fE) (E gE) = E $
  do f <- fE
     g <- gE
     s <- readEnvM
     return $ note "ifE" $ proc (cin, ienv, c) ->
       do -- If this statement is active then make a choice, otherwise don't (t=tt).
          t <- (| unsafeNonDetInstAC (\x -> (| orAC (returnA -< ciGo cin) (returnA -< x) |) ) |)
          t_go <- andA -< (ciGo cin, t)
          e_go <- andA <<< second notA -< (ciGo cin, t)
          (t_cout, t_env, _t_d) <- f -< (cin{ciGo = t_go}, ienv, c)
          (e_cout, e_env, _e_d) <- g -< (cin{ciGo = e_go}, ienv, c)
          oenv <- combine_envs s -< (t_env, e_env)
          exns' <- lift2 (exnID s) orA -< (coExns t_cout, coExns e_cout)
          selected <- orA -< (coSelected t_cout, coSelected e_cout)
          terminated <- orA -< (coTerminated t_cout, coTerminated e_cout)
          paused <- orA -< (coPaused t_cout, coPaused e_cout)
          returnA -< ( Cout { coSelected = selected
                            , coTerminated = terminated
                            , coPaused = paused
                            , coExns = exns' }
                     , oenv
                     , () )
-}

-------------------------------------------------------------------
-- Exceptions.
-------------------------------------------------------------------

newtype Exception = Exception Int

-- | Allocate a scoped local 'Exception'.
catchE :: forall (~>) env b. EC (~>) => (Exception -> E (~>) env b)
       -> E (~>) env b
catchE fE = E $
  do s <- readEnvM
     let eid = exnID s
         s' = s{exnID = succ eid}
     f <- inEnvEM s' (unE (fE (Exception eid)))
     return $ note ("catchE: " ++ show eid) $ proc (cin, ienv, env) ->
       do rec kill <- orA -< (ciKill cin, e_thrown)
              (f_cout, f_env, b) <- f -< (cin{ciKill = kill}, ienv, env)
              let !(exns :> e_thrown) = Seq.viewr (coExns f_cout)
          term <- orA -<
                  -- trace ("catchE: coExns len: " ++ show (Seq.length (coExns f_cout)) ++ " / s: " ++ show s) $
                  (coTerminated f_cout, e_thrown)
          returnA -< ( f_cout{coTerminated = term, coExns = exns}
                     , f_env
                     , b )

-- | Throw an 'Exception'.
throwE :: forall (~>) env. EC (~>) => Exception -> E (~>) env ()
throwE (Exception eid) = E $
  do s <- readEnvM
     return $ note ("throwE: " ++ show eid) $ proc (cin, _ienv, _c) ->
       do ff <- falseA -< ()
          let (oenv, exns) = cenv_exns_empty s ff
          returnA -< ( Cout { coSelected = ff
                            , coTerminated = ff
                            , coPaused = ff
                            , coExns = Seq.update eid (ciGo cin) exns }
                     , oenv
                     , () )

-------------------------------------------------------------------
-- Pre-emption (abort/when, previously do/watching (>>)).
-- Intended to be used infix.
-------------------------------------------------------------------

-- FIXME get names straight

abortE :: EC (~>) => E (~>) env c -> Signal -> E (~>) env c
abortE fE s = proc env ->
  do c <- sigE s -< ()
     (| abort_primE (returnA -< c) (fE -< env) |)

abortE' :: EC (~>) => E (~>) env (B (~>)) -> E (~>) env c -> E (~>) env c
abortE' condE fE = proc env ->
  do c <- condE -< env
     (| abort_primE (returnA -< c) (fE -< env) |)

-- | The combinational loop involves the 'abortE' @coTerminated@
-- output, I think. See test 112 for an example that loops if we use
-- 'loop'.
abort_primE :: EC (~>) => (env ~> B (~>)) -> E (~>) env c -> E (~>) env c
abort_primE cond (E fE) = E $
  do f <- fE
     return $ note "abortE" $ proc (cin, ienv, env) ->
       do c <- cond -< env
          ((f_cout, f_env, d), t) <-
            (| combLoop (\selected ->
                 do t <- andA -< (selected, ciRes cin)
                    res <- andA <<< second notA -< (t, c)
                    fout@(f_cout, _f_env, _d) <- f -< (cin{ciRes = res}, ienv, env)
                    returnA -< ((fout, t), coSelected f_cout) ) |)
          terminated <- orA <<< second andA -< (coTerminated f_cout, (c, t))
          returnA -< (f_cout{coTerminated = terminated}, f_env, d)

-------------------------------------------------------------------
-- Suspend.
-------------------------------------------------------------------

-- | Suspend on a boolean signal.
-- FIXME semantics.
-- FIXME verify acyclic.
suspendE :: (ArrowComb (~>), ArrowLoop (~>))
         => E (~>) gin gout
         -> E (~>) (gin, B (~>)) gout
suspendE f = error "suspendE"
{-
  MkE $ \s e ->
    let
      arrowF = runE f s e
      arrow =
        proc (cin, (gin, cond)) ->
          do rec t0 <- andA -< (sel', eciRes cin)
                 res' <- andA <<< second notA -< (t0, cond)
                 t1   <- andA -< (t0, cond)
                 susp' <- orA -< (eciSusp cin, t1)
                 let cin' = cin{ eciRes = res', eciSusp = susp' }
                 (cout@(MkECout { ecoSelected = sel'}), gout)
                     <- arrowF -< (cin', gin)
             paused' <- orA -< (ecoPaused cout, t1)
             returnA -< (cout { ecoPaused = paused' }, gout)
    in arrow
-}

-------------------------------------------------------------------
-- Knowledge.
-------------------------------------------------------------------

{-

Knowledge gets messy in concert with combinational cycles.

-}

kTestE :: (EC (~>), ArrowKTest (~>))
         => KF -> E (~>) env () -> E (~>) env () -> E (~>) env ()
kTestE kf = ifE (kTest kf)

agentE :: ArrowAgent (~>) (Cin (B (~>)), Esigs (B (~>)), obs)
       => AgentID -> E (~>) obs action -> E (~>) obs action
agentE aid (E fA) = E $ fmap (agent aid) fA

-- | Probe a value.
probeE :: (EC (~>), ArrowProbe (~>) v)
       => String -> E (~>) v v
probeE = lift . probeA

-- | Probe a "Signal".
probeSigE :: (EC (~>), ArrowProbe (~>) (B (~>)))
          => String -> Signal -> E (~>) env ()
probeSigE l s = sigE s >>> probeE l >>> arr (const ())

-------------------------------------------------------------------

-- | Often we want to emit a signal until a computation has finished.
--
-- More precisely, we want to emit it while control resides with the
-- computation, i.e. when it pauses. If the computation does not pause
-- then the signal never gets emitted.
--
-- We aim to do this without extra state.
--
-- FIXME we want this to work with both E and bus signals, so we might
-- have to consider ciGo too.
sustainWhileE :: forall (~>) env. EC (~>) => Signal -> E (~>) env () -> E (~>) env ()
sustainWhileE (Signal sid) (E fE) = E $
  do f <- fE
     return $ proc (cin, ienv, c) ->
       do (f_cout, f_env, d) <- f -< (cin, ienv, c)
          -- active <- orA -< (ciGo cin, coPaused f_cout)
          let active = coPaused f_cout
          sval <- orA -< (eSigs f_env `Seq.index` sid, active)
          let oenv = Seq.update sid sval (eSigs f_env)
          returnA -< (f_cout, f_env{eSigs = oenv}, d)

-------------------------------------------------------------------
-- Debugging
-------------------------------------------------------------------

-- | Add a probe: true if this statement is active.
activeE :: forall (~>) v. (EC (~>), ArrowProbe (~>) (B (~>)))
        => ProbeID -> E (~>) v v
activeE pid = E $
  do s <- readEnvM
     return $ proc (cin, _ienv, c) ->
       do probeA pid -< ciGo cin
          ff <- falseA -< ()
          let (oenv, exns) = cenv_exns_empty s ff
          returnA -< ( Cout { coSelected = ff
                            , coTerminated = ciGo cin
                            , coPaused = ff
                            , coExns = exns }
                     , oenv
                     , c)

-------------------------------------------------------------------
-- Esterel top-level.
-------------------------------------------------------------------

-- | FIXME top-level.
-- FIXME assert something about f_env
runE' :: EC (~>) => E (~>) c d -> (c ~> (B (~>), d))
runE' fE = note "runE" $ proc c ->
  do boot <- isInitialState -< ()
     ff <- falseA -< ()
     tt <- trueA -< ()
     let cin = Cin { ciGo = boot
                   , ciRes = tt
                   , ciSusp = ff
                   , ciKill = ff
                   }
     (f_cout, f_env, d) <- f -< (cin, e0, c)
     returnA -<
       -- trace ("runE': coExns: " ++ show (Seq.length (coExns f_cout))
       --        ++ " sigs: " ++ show (Seq.length (eSigs f_env)))
       assert (Seq.length (coExns f_cout) == 0) $
       assert (Seq.length (eSigs f_env) == 0) $
       (coTerminated f_cout, d)
  where
    e0 = Esigs {eSigs = Seq.empty}
    s0 = Static {exnID = 0, sigID = 0}
    f = runEnvM (unE fE) s0
