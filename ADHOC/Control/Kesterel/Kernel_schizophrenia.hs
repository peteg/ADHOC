{- The guts of the arrowized Esterel circuit translation.
 - Copyright   :  (C)opyright 2006, 2009 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -
 - The 'E' arrow acts as an /environment transformer/.
 -
 - Sketch following Berry, CONSTRUCTIVE SEMANTICS OF ESTEREL.
 -
 - Representation: use unboxed mutable (fusable?) arrays for the bit sets?
 -
 - Invariants:
 -  completion codes are one-hot p113.
 -
 - FIXME SeqA.zip/SeqA.unzip for environments are too strict.

This version tries to deal with schizophrenia. Berry's level ideas
don't play nicely with circuits (e.g. probes and kbpTests get
duplicated) so we revert to his simpler semantics that does not treat
this issue.

 -}
module ADHOC.Control.Kesterel.Kernel where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude ()

import Data.Map ( Map )
import qualified Data.Map as Map

import Data.Set ( Set )
import qualified Data.Set as Set

import ADHOC.Circuits hiding ( sin )
import ADHOC.Model	( ArrowProbe(..) )
import ADHOC.NonDet

import ADHOC.SeqA ( SeqA )
import qualified ADHOC.SeqA as SeqA

-- import ADHOC.Generics
-- import ADHOC.Data.Patterns

-------------------------------------------------------------------
-- Esterel translation boilerplate.
-- Note we carefully separate static (structural) and dynamic things.
-- These 'Int' wrappers help keep things straight.
-------------------------------------------------------------------

-- | Level: number of enclosing 'signalE' and '(||||)' statements.
newtype Level = Level Int
    deriving (Enum, Eq, Num, Ord, Show)

instance Bounded Level where
    minBound = Level 0
    maxBound = Level maxBound

-- | Exception ID/counter. Note the order is flipped so we get the
-- priority story correct (see 'catchE').
newtype ExnID = ExnID { unExnID :: Int }
    deriving (Enum, Eq, Show)

instance Bounded ExnID where
    minBound = ExnID 0
    maxBound = ExnID maxBound

-- FIXME careful, this might screw Ord uses in SeqA.
instance Ord ExnID where
    compare (ExnID x) (ExnID y) = compare y x

-- | Signal ID/counter.
newtype SigID = SigID Int
    deriving (Enum, Eq, Ord, Show)

instance Bounded SigID where
    minBound = SigID 0
    maxBound = SigID maxBound

-- | Structural (static) translation context. Berry's /rho/.
data Sin
    = Sin
      { siExns :: SeqA ExnID Level -- ^ Map exceptions in scope to
                                   -- their level of definition. Size
                                   -- tracks the maximal exceptional
                                   -- completion code.
      , siSigs :: SeqA SigID Level -- ^ Map local signals in scope to
                                   -- their level of definition. Size
                                   -- tracks signal id's.
      , siLevel :: Level -- ^ The number of enclosing 'signalE' and
                         -- '(||||)'. FIXME *** number of current
                         -- level.
      }

-- | Static description of a sub-circuit. All fields mandatory.
data Sout
    = Sout
      { soPauses :: Bool -- ^ Can pause
      , soEmits :: Set SigID -- ^ Emitted signals (sparse?)
      , soThrows :: Set ExnID -- ^ Thrown exceptions (sparse?)
      }

-- | Dynamic control inputs for 'E' sub-circuits.
data Cin b
    = Cin
      { ciGo :: SeqA Level b -- ^ Enabled for reincarnation level /i/
      , ciRes :: b
      , ciSusp :: b
      , ciKill :: SeqA Level b -- ^ Killed for reincarnation level /i/
      , ciSigs :: SeqA SigID (SeqA Level b) -- ^ Values for the
                                            -- signals in scope,
                                            -- represented with one
                                            -- bit per reincarnation
                                            -- level
      } deriving Show

-- | Dynamic control outputs for 'E' sub-circuits. Mandatory: 'coSel', 'coTerm'.
data Cout b
    = Cout
      { coSel :: b -- ^ Selected (FIXME an enclosed 'pause' is paused.)
      , coTerm :: SeqA Level b -- ^ Terminated at reincarnation level /i/
      , coPaused :: SeqA Level b -- ^ Paused at reincarnation level /i/
      , coExns :: Map ExnID (SeqA Level b) -- ^ Completion level at
                                           -- reincarnation level /i/
                                           -- (inner) for each
                                           -- exception in scope.
      , coSigs :: Map SigID (SeqA Level b) -- ^ Values for the
                                           -- signals in scope. FIXME sparse?
      } deriving Show

-- | Dynamic behaviour of a sub-circuit.
type Dynamic (~>) c d
    = (Cin (B (~>)), SeqA Level c) ~> (Cout (B (~>)), SeqA Level d)

-- | The @E@ arrow.
newtype E (~>) c d = E { unE :: Sin -> (Sout, Dynamic (~>) c d) }

-- | Lift up computations in the underlying arrow.
instance ArrowComb (~>) => ArrowTransformer E (~>) where
    lift = liftE

instance ArrowComb (~>) => Category (E (~>)) where
    id = lift id
    f . g = seqE g f

-- FIXME first can be implemented much more efficiently
instance ArrowComb (~>) => Arrow (E (~>)) where
    arr = lift . arr
    first f = f *** id
    (***) = seqEparEnv

instance (ArrowComb (~>), ArrowLoop (~>))
      => ArrowLoop (E (~>)) where
    loop = arrowLoopE

-------------------------------------------------------------------
-- Lifting and looping.
-------------------------------------------------------------------

-- | Esterel's 'nothingE': lifts an underlying arrow /f/, which is
-- executed at every instant. FIXME non-linear use of /f/: test where
-- this is actually useful?
liftE :: ArrowComb (~>)
      => (c ~> d) -> E (~>) c d
liftE f =
  E $ \sin ->
      ( Sout { soPauses = False
             , soEmits = Set.empty
             , soThrows = Set.empty
             }
      , proc (cin, c) ->
          do d <- SeqA.lift (siLevel sin) f -< c
             cFalse <- falseA -< ()
             returnA -< ( Cout { coSel = cFalse
                               , coTerm = ciGo cin }
                        , d)
      )

-- | Does nothing, consumes no time.
nothingE :: ArrowComb (~>) => E (~>) v v
nothingE = id

-- | Data recursion: hoist up an underlying instance of
-- 'ArrowLoop'. Otherwise oblivious to the 'E' shenanigans.
-- FIXME strictness of unzip?
arrowLoopE :: ArrowLoop (~>)
           => E (~>) (b, d) (c, d) -> E (~>) b c
arrowLoopE f =
  E $ \sin ->
    let (f_s, f_d) = unE f sin
     in ( f_s
        , proc (cin, b) ->
            do rec ~(cout, cd) <- f_d -< (cin, SeqA.zip b d)
                   let ~(c, d) = SeqA.unzip cd
               returnA -< (cout, c)
        )

-------------------------------------------------------------------
-- Kernel 'Arrow' machinery: sequential composition.
-------------------------------------------------------------------

-- | FIXME move. Based on a predicate of the static information,
-- either use or combine some stuff.
so_combine :: Arrow (~>)
           => (t -> Bool) -> t -> t -> ((b, b) ~> b) -> (b, b) ~> b
so_combine proj sc0 sc1 combA =
    case (proj sc0, proj sc1) of
      (False, False) -> arr (const (error "FIXME static info says you shouldn't demand this."))
      (True, False)  -> arr fst
      (False, True)  -> arr snd
      (True, True)   -> combA

-- | FIXME combine signals. Check carefully: the vectors may be of different length.
combineSigs :: ArrowComb (~>)
            => SeqA SigID Level
            -> Sout
            -> Sout
            -> [SigID]
            -> ( Map SigID (SeqA Level (B (~>)))
               , Map SigID (SeqA Level (B (~>))) ) ~> Map SigID (SeqA Level (B (~>)))
combineSigs sigLevels f_s g_s = go
  where
    err = error $ "FIXME combineSigs scope screwup"

    go [] = arr (const Map.empty)
    go (sid:sids) =
      proc fg_sigs@(f_sigs, g_sigs) ->
        (| (liftA2 (Map.insert sid))
                   (so_combine ((sid `Set.member`) . soEmits)
                               f_s g_s
                               (SeqA.disjoin (sigLevels `SeqA.index` sid))
                                   -< ( Map.findWithDefault err sid f_sigs
                                      , Map.findWithDefault err sid g_sigs ))
                   (go sids -< fg_sigs) |)

-- | FIXME combine exceptions.
combineExns :: ArrowComb (~>)
            => Level
            -> Sout
            -> Sout
            -> [ExnID]
            -> ( Map ExnID (SeqA Level (B (~>)))
               , Map ExnID (SeqA Level (B (~>))) ) ~> Map ExnID (SeqA Level (B (~>)))
combineExns l f_s g_s = go
  where
    err eid = error $ "FIXME combineExns scope screwup for " ++ show eid

    go [] = arr (const Map.empty)
    go (eid:eids) =
      proc fg_exns@(f_exns, g_exns) ->
        (| (liftA2 (Map.insert eid))
                   (so_combine ((eid `Set.member`) . soThrows)
                               f_s g_s
                               (SeqA.disjoin l)
                                   -< ( Map.findWithDefault (err eid) eid f_exns
                                      , Map.findWithDefault (err eid) eid g_exns ))
                   (go eids -< fg_exns) |)

-- | The control part of sequential composition.
seqE_cout :: ArrowComb (~>)
          => Sin -> Sout -> Sout
          -> (Sout, (Cout (B (~>)), Cout (B (~>))) ~> Cout (B (~>)))
seqE_cout sin f_s g_s =
    let l = siLevel sin
        emittedSigs = soEmits f_s `Set.union` soEmits g_s
        thrownExns = soThrows f_s `Set.union` soThrows g_s
        dyn =
          proc (f_cout, g_cout) ->
            do sel <- orA -< (coSel f_cout, coSel g_cout)
               paused <- so_combine soPauses f_s g_s (SeqA.disjoin l)
                         -< (coPaused f_cout, coPaused g_cout)
               -- FIXME correct.
               sigs   <- combineSigs (siSigs sin) f_s g_s (Set.toList emittedSigs)
                         -< (coSigs f_cout, coSigs g_cout)
               exns   <- combineExns l f_s g_s (Set.toList thrownExns)
                         -< (coExns f_cout, coExns g_cout)
               returnA -< Cout { coSel = sel
                               , coTerm = coTerm g_cout
                               , coPaused = paused
                               , coExns = exns
                               , coSigs = sigs
                               }
    in ( Sout { soPauses = soPauses f_s || soPauses g_s
              , soEmits  = emittedSigs
              , soThrows = thrownExns
              }
       , dyn )

-- | Sequential composition of two 'E' computations, chaining the data
-- output of the first into the second.
seqE :: ArrowComb (~>)
     => E (~>) c d -> E (~>) d e -> E (~>) c e
f `seqE` g =
  E $ \sin ->
    let (f_s, f_d) = unE f sin
        (g_s, g_d) = unE g sin
        (s, cout_d) = seqE_cout sin f_s g_s

        dyn = -- note "seqE" $ -- FIXME we use this all the time, too many boxes in graphviz...
          proc (cin, c) ->
            do (f_cout, d) <- f_d -< (cin, c)
               (g_cout, e) <- g_d -< (cin{ciGo = coTerm f_cout}, d)
               first cout_d -< ((f_cout, g_cout), e)
    in (s, dyn)

-- | Sequential composition of two 'E' computations, with separate
-- data environments (for '(***)').
seqEparEnv :: ArrowComb (~>)
           => E (~>) c  d
           -> E (~>) c' d'
           -> E (~>) (c, c') (d, d')
f `seqEparEnv` g =
  E $ \sin ->
    let (f_s, f_d) = unE f sin
        (g_s, g_d) = unE g sin
        (s, cout_d) = seqE_cout sin f_s g_s

        dyn = -- note "seqEparEnv" $ FIXME graphviz
          proc (cin, cd) ->
            do let (c, d) = SeqA.unzip cd
               (f_cout, c') <- f_d -< (cin, c)
               (g_cout, d') <- g_d -< (cin{ciGo = coTerm f_cout}, d)
               first cout_d -< ((f_cout, g_cout), SeqA.zip c' d')
    in (s, dyn)

-------------------------------------------------------------------
-- Parallel composition.
-------------------------------------------------------------------

infixr 2 ||||

(||||) :: ArrowComb (~>)
       => E (~>) c d -> E (~>) c d' -> E (~>) c (d, d')
(||||) = parE

-- | Parallel composition. Think of this as "control-parallelism", not
-- the "data-parallelism" provided by 'seqEsepEnvs'.
parE :: ArrowComb (~>)
     => E (~>) c d -> E (~>) c d' -> E (~>) c (d, d')
f `parE` g =
  E $ \sin ->
    let l  = siLevel sin
        l' = succ l
        sin' = sin{ siLevel = l' }

        (f_s, f_d) = unE f sin'
        (g_s, g_d) = unE g sin'

        emittedSigs = soEmits f_s  `Set.union` soEmits g_s
        thrownExns  = soThrows f_s `Set.union` soThrows g_s

        dyn = note "parE" $
          proc (cin, c) ->
            do cFalse <- falseA -< ()
               let cin' = cin { ciGo = ciGo cin SeqA.|> cFalse -- FIXME explain p151
                              , ciKill = ciKill cin SeqA.|> (ciKill cin `SeqA.index` l)
                              }
                   c' = c SeqA.|> (c `SeqA.index` l)
               (f_cout, d)  <- f_d -< (cin', c')
               (g_cout, d') <- g_d -< (cin', c')

               sel <- orA -< (coSel f_cout, coSel g_cout)

               -- FIXME describe: Not being selected (i.e. already
               -- terminated) is the same as terminating ???
               f_term_l' <- orA <<< first notA -< (coSel f_cout, coTerm f_cout `SeqA.index` l')
               let f_term' = SeqA.update (coTerm f_cout) l' f_term_l'

               g_term_l' <- orA <<< first notA -< (coSel g_cout, coTerm g_cout `SeqA.index` l')
               let g_term' = SeqA.update (coTerm g_cout) l' g_term_l'

               (term, paused, exns)
                 <- synchronise l' f_s g_s (Set.toList thrownExns)
                   -< ( (f_term', coPaused f_cout, coExns f_cout)
                      , (g_term', coPaused g_cout, coExns g_cout) )

               -- FIXME correct.
               sigs <- combineSigs (siSigs sin) f_s g_s (Set.toList emittedSigs)
                         -< (coSigs f_cout, coSigs g_cout)

               -- FIXME need to fold the new depth (l') into the old depth (l).
               let dout = SeqA.zip d d'
--                dd <- muxA -< -- trace ("signalE: " ++ show (l, SeqA.length (ciGo cin), SeqA.length d)) $
--                              ( ciGo cin `SeqA.index` l
--                              , (d `SeqA.index` l, d `SeqA.index` succ l))
--                let d' = SeqA.take d l SeqA.|> dd

               returnA -< ( Cout { coSel = sel
                                 , coTerm = term
                                 , coPaused = paused
                                 , coExns = exns
                                 , coSigs = sigs
                                 }
                          , dout )
    in ( Sout { soPauses = soPauses f_s || soPauses g_s
              , soEmits  = emittedSigs
              , soThrows = thrownExns
              }
       , dyn )

----------------------------------------

-- | Synchronisation, following Berry p152. Compute the completion
-- code of the two threads.
synchronise l' f_s g_s fg_exns =
  proc ( (f_term, f_paused, f_exns)
       , (g_term, g_paused, g_exns) ) ->
    do term <- SeqA.conjoin l' -< (f_term, g_term)

       -- FIXME test: throw exception in parallel with pauseE
       -- this has got to break somehow due to the error in sync_combine

       arghFIXME <-
         SeqA.lift3 l' (sync_combine (soPauses f_s) (soPauses g_s))
           -< ( SeqA.zip f_term g_term, f_paused, g_paused )

       let (pn, paused) = SeqA.unzip arghFIXME
       exns <- sync_combineExns l' f_s g_s fg_exns -< (pn, (f_exns, g_exns))

       -- FIXME p152 last line: patch up l, l' for all completion codes.

       returnA -< (term, paused, exns)

-- | FIXME this should be rowA for SeqA.
sync_combineExns l' f_s g_s = go
  where
    err = error $ "FIXME sync_combineExns scope screwup"

    cmb eid = sync_combine (eid `Set.member` soThrows f_s)
                           (eid `Set.member` soThrows g_s)

    -- FIXME rowA?
    go [] = arr (const Map.empty)
    go (eid:eids) =
      proc (prev, fg_exns@(f_exns, g_exns)) ->
        do arghFIXME <- SeqA.lift3 l' (cmb eid)
                            -< ( prev
                               , Map.findWithDefault err eid f_exns
                               , Map.findWithDefault err eid g_exns )
           let (next, exn) = SeqA.unzip arghFIXME
           exns <- go eids -< (next, fg_exns)
           returnA -< Map.insert eid exn exns

-- | FIXME rename f_throws: inc f_pauses
sync_combine f_throws g_throws =
    case (f_throws, g_throws) of
      (False, False) -> max_neither -- needed only for the pauses case.
      (True, False)  -> max_l_only
      (False, True)  -> max_r_only
      (True, True)   -> max_both

-- | Neither sub-circuit pauses.
max_neither =
  arr $ \ ((lprev, rprev), _lexn, _rexn) ->
          ((lprev, rprev), error $ "FIXME max_neither you shouldn't be demanding this.")

-- FIXME exception thrown by the left circuit but not the right.
max_l_only =
  proc ((lprev, rprev), lexn, _rexn) ->
    do lnext <- orA  -< (lprev, lexn)
       exn   <- andA -< (lnext, rprev)
       returnA -< ((lnext, rprev), exn)

-- FIXME exception thrown by the right circuit but not the left.
max_r_only =
  proc ((lprev, rprev), _lexn, rexn) ->
    do rnext <- orA  -< (rprev, rexn)
       exn   <- andA -< (lprev, rnext)
       returnA -< ((lprev, rnext), exn)

max_both =
  proc ((lprev, rprev), lexn, rexn) ->
    do lnext    <- orA -< (lprev, lexn)
       rnext    <- orA -< (rprev, rexn)
       exn_both <- orA -< (lnext, rnext)
       exn      <- andA <<< second andA -< (exn_both, (lnext, rnext))
       returnA -< ((lnext, rnext), exn)

-------------------------------------------------------------------
-- Kernel Esterel machinery.
-------------------------------------------------------------------

-- | Rest here for an instant.
pauseE :: (ArrowComb (~>), ArrowDelay (~>) (B (~>)), ArrowLoop (~>))
       => E (~>) c c
pauseE =
  E $ \sin ->
    let l = siLevel sin

        dyn = note "pauseE" $
          proc (cin, c) ->
            do nKill <- SeqA.not l -< ciKill cin
               gk <- SeqA.disjoinF l <<< SeqA.conjoin l -< (ciGo cin, nKill)
               nkl <- notA -< ciKill cin `SeqA.index` l
               rec srnk <- andA <<< second andA -< (ciSusp cin, (reg, nkl))
                   reg <- (| delayAC (falseA -< ()) (orA -< (srnk, gk)) |)
               term_l <- andA -< (reg, ciRes cin)
               -- FIXME abstract
               term <- SeqA.initialise l (\i -> if i == l then id else arr (const ()) >>> falseA) -< term_l
               returnA -< ( Cout { coSel = reg
                                 , coTerm = term
                                 , coPaused = ciGo cin }
                          , c )
    in ( Sout { soPauses = True
              , soEmits = Set.empty
              , soThrows = Set.empty
              }
       , dyn )

-- | Infinitely loop.
-- FIXME not correct for unsafe loops?
-- This definitely requires ArrowCombLoop.
loopE :: (ArrowComb (~>), ArrowCombLoop (~>) (B (~>)))
      => E (~>) c d
      -> E (~>) c d
loopE f =
  E $ \sin ->
    let l = siLevel sin
        (f_s, f_d) = unE f sin

        dyn = note "loopE" $
          proc (cin, c) ->
            (| combLoop (\term ->
                 do f_go_l <- orA -< (ciGo cin `SeqA.index` l, term)
                    (f_cout, d) <- f_d -< (cin{ciGo = SeqA.update (ciGo cin) l f_go_l}, c)
                    cFalse <- falseA -< ()
                    -- Careful here: this statement never terminates.
                    returnA -< ( (f_cout{coTerm = SeqA.update (coTerm f_cout) l cFalse}, d)
                               , coTerm f_cout `SeqA.index` l ) ) |)
    in (f_s, dyn) -- FIXME verify

-------------------------------------------------------------------
-- Local signals.
-------------------------------------------------------------------

-- | User-visible signals.
newtype Signal s = Signal SigID

-- | Allocate a scoped local 'Signal'.
signalE :: (ArrowComb (~>), ArrowCombLoop (~>) (B (~>)), ArrowMux (~>) d)
        => (forall s. Signal s -> (E (~>) c d))
        -> E (~>) c d
signalE f =
  E $ \sin ->
    let sigs = siSigs sin
        sid  = SeqA.length sigs
        sig  = Signal sid

        l  = siLevel sin
        l' = succ l
        sin' = sin{ siSigs = sigs SeqA.|> l'
                  , siLevel = l' }

        (f_s, f_d) = unE (f sig) sin'

        err = error $ "FIXME signalE is screwed, signal not in cout: " ++ show sid

        -- If the signal is not emitted, no need for the combLoop -
        -- the signal vector is constantly false.
        -- FIXME improvement: add soTested and optimise presentE (etc)
        sigLoop
            | sid `Set.member` soEmits f_s = SeqA.combLoopF l'
            | otherwise =
                \g -> proc env ->
                  do sv <- SeqA.initialise l' (const falseA) -< ()
                     arr fst <<< g -< (env, sv)

        dyn =
          sigLoop $ note "signalE" $ proc ((cin, c), sv) ->
            do cFalse <- falseA -< ()
               let cin' = cin { ciGo = ciGo cin SeqA.|> cFalse -- FIXME explain
                              , ciKill = ciKill cin SeqA.|> (ciKill cin `SeqA.index` l)
                              , ciSigs = ciSigs cin SeqA.|> sv
                              }
                   -- Fan out the incoming environment.
                   c' = c SeqA.|> (c `SeqA.index` l)
               (f_cout, d) <- f_d -< (cin', c')
               -- FIXME which environment to return?
               -- FIXME correct If we're resuming, use the depth, otherwise use the (last??) surface.
               -- FIXME take care of suspend
               dd <- muxA -< -- trace ("signalE: " ++ show (l, SeqA.length (ciGo cin), SeqA.length d)) $
                             ( ciGo cin `SeqA.index` l
                             , (d `SeqA.index` l, d `SeqA.index` succ l))
               let d' = SeqA.take d l SeqA.|> dd

               returnA -< -- trace ("signalE final: " ++ show (SeqA.length d')) $
                          ( ( f_cout{coSigs = sid `Map.delete` coSigs f_cout} -- FIXME verify
                            , d' )
                          , Map.findWithDefault err sid (coSigs f_cout) )

    in (f_s, dyn) -- FIXME verify statics

-- | Emit a 'Signal'.
emitE :: ArrowComb (~>)
      => Signal s -> E (~>) v v
emitE (Signal sid) =
  E $ \sin ->
    let l = siLevel sin
        sl = siSigs sin `SeqA.index` sid

        -- Fold level i > l(s) into l(s) p149.
        -- FIXME requires Num instance for Level
        disj ldiff =
          proc go ->
            do let (sa, sb) = go `SeqA.splitAt` sl
               sb' <- SeqA.disjoinF ldiff -< -- trace ("emitE disj: " ++ show (l, sl, ldiff, SeqA.length sa, SeqA.length sb)) $
                                             sb
               returnA -< sa SeqA.|> sb'

        dyn =
          proc (cin, c) ->
            do cFalse <- falseA -< ()
               sv <- (case l - sl of
                       0 -> returnA
                       x -> disj x) -< ciGo cin
               returnA -< ( Cout { coSel = cFalse
                                 , coTerm = ciGo cin
                                 , coSigs = Map.singleton sid sv
                                 }
                          , c )
    in ( Sout { soPauses = False
              , soEmits = Set.singleton sid
              , soThrows = Set.empty
              }
       , dyn )

-- | Test for the presence of a signal.
-- FIXME common up with 'ifE'
-- FIXME which environment do we use if "neg go" ?
presentE :: (ArrowComb (~>), ArrowMux (~>) d)
         => Signal s
         -> E (~>) c d
         -> E (~>) c d
         -> E (~>) c d
presentE (Signal sid) thenE elseE =
  E $ \sin ->
    let l = siLevel sin
        sl = siSigs sin `SeqA.index` sid

        (then_s, then_d) = unE thenE sin
        (else_s, else_d) = unE elseE sin

        emittedSigs = soEmits then_s `Set.union` soEmits else_s
        thrownExns = soThrows then_s `Set.union` soThrows else_s

        dyn = note "presentE" $
          proc (cin, c) ->
            do let sv = ciSigs cin `SeqA.index` sid
               -- Take care of when siLevel > signal level
               t_go <- SeqA.conjoinUpTo l sl -< (ciGo cin, sv)
               e_go <- SeqA.conjoinUpTo l sl <<< second (SeqA.not sl) -< (ciGo cin, sv)
               (then_cout, t_d) <- then_d -< (cin{ciGo = t_go}, c)
               (else_cout, e_d) <- else_d -< (cin{ciGo = e_go}, c)

               -- Again, take care of siLevel > signal level
               d <- SeqA.lift3UpTo sl l l muxA' -< (sv, t_d, e_d)

               sel    <- orA -< (coSel then_cout, coSel else_cout)
               paused <- so_combine soPauses then_s else_s (SeqA.disjoin l)
                         -< (coPaused then_cout, coPaused else_cout)
               term   <- SeqA.disjoin l -< (coTerm then_cout, coTerm else_cout)

               sigs  <- combineSigs (siSigs sin) then_s else_s (Set.toList emittedSigs)
                         -< (coSigs then_cout, coSigs else_cout)

               exns   <- combineExns l then_s else_s (Set.toList thrownExns)
                         -< (coExns then_cout, coExns else_cout)

               returnA -< ( Cout { coSel = sel
                                 , coTerm = term
                                 , coPaused = paused
                                 , coExns = exns
                                 , coSigs = sigs
                                 }
                          , d )
    in ( Sout { soPauses = soPauses then_s || soPauses else_s
              , soEmits  = emittedSigs
              , soThrows = thrownExns
              }
       , dyn )

-- | Branch on an arbitrary test.  FIXME stateful tests: feed in the
-- go bit? Note this works as-is, but may not be useful. The test
-- logic is duplicated at each level, so state is a bit messy.
--
-- This probably only works for stateless tests, otherwise we're
-- fighting levels by duplicating state.
ifE :: (ArrowComb (~>), ArrowMux (~>) d)
    => (c ~> B (~>))
    -> E (~>) c d
    -> E (~>) c d
    -> E (~>) c d
ifE test thenE elseE =
  E $ \sin ->
    let l = siLevel sin

        (then_s, then_d) = unE thenE sin
        (else_s, else_d) = unE elseE sin

        emittedSigs = soEmits then_s `Set.union` soEmits else_s
        thrownExns = soThrows then_s `Set.union` soThrows else_s

        dyn = note "ifE" $
          proc (cin, c) ->
            do -- Duplicate the test logic.
               cv <- SeqA.lift l test -< c
               t_go <- SeqA.conjoin l -< (ciGo cin, cv)
               e_go <- SeqA.conjoin l <<< second (SeqA.not l) -< (ciGo cin, cv)
               (then_cout, t_d) <- then_d -< (cin{ciGo = t_go}, c)
               (else_cout, e_d) <- else_d -< (cin{ciGo = e_go}, c)

               d <- SeqA.lift3 l muxA' -< (cv, t_d, e_d)

               sel    <- orA -< (coSel then_cout, coSel else_cout)
               paused <- so_combine soPauses then_s else_s (SeqA.disjoin l)
                         -< (coPaused then_cout, coPaused else_cout)
               term   <- SeqA.disjoin l -< (coTerm then_cout, coTerm else_cout)

               sigs   <- combineSigs (siSigs sin) then_s else_s (Set.toList emittedSigs)
                         -< (coSigs then_cout, coSigs else_cout)

               exns   <- combineExns l then_s else_s (Set.toList thrownExns)
                         -< (coExns then_cout, coExns else_cout)

               returnA -< ( Cout { coSel = sel
                                 , coTerm = term
                                 , coPaused = paused
                                 , coExns = exns
                                 , coSigs = sigs
                                 }
                          , d )
    in ( Sout { soPauses = soPauses then_s || soPauses else_s
              , soEmits  = emittedSigs
              , soThrows = thrownExns
              }
       , dyn )

-- | Branch on an arbitrary test. FIXME maybe 'ifE' is not
-- useful. This isn't so great either, as the test can't depend on the
-- environment.
--
-- Note that we do not pass the environment to the test, so it must be
-- stateful to be interesting. We don't need to duplicate it at each level.
ifE' :: (ArrowComb (~>), ArrowMux (~>) d)
     => (() ~> B (~>))
     -> E (~>) c d
     -> E (~>) c d
     -> E (~>) c d
ifE' test thenE elseE =
  E $ \sin ->
    let l = siLevel sin

        (then_s, then_d) = unE thenE sin
        (else_s, else_d) = unE elseE sin

        emittedSigs = soEmits then_s `Set.union` soEmits else_s
        thrownExns = soThrows then_s `Set.union` soThrows else_s

        dyn = note "ifE" $
          proc (cin, c) ->
            do cv0 <- test -< ()
               let cv = SeqA.replicate l cv0
               t_go <- SeqA.conjoin l -< (ciGo cin, cv)
               e_go <- SeqA.conjoin l <<< second (SeqA.not l) -< (ciGo cin, cv)
               (then_cout, t_d) <- then_d -< (cin{ciGo = t_go}, c)
               (else_cout, e_d) <- else_d -< (cin{ciGo = e_go}, c)

               d <- SeqA.lift3 l muxA' -< (cv, t_d, e_d)

               sel    <- orA -< (coSel then_cout, coSel else_cout)
               paused <- so_combine soPauses then_s else_s (SeqA.disjoin l)
                         -< (coPaused then_cout, coPaused else_cout)
               term   <- SeqA.disjoin l -< (coTerm then_cout, coTerm else_cout)

               sigs   <- combineSigs (siSigs sin) then_s else_s (Set.toList emittedSigs)
                         -< (coSigs then_cout, coSigs else_cout)

               exns   <- combineExns l then_s else_s (Set.toList thrownExns)
                         -< (coExns then_cout, coExns else_cout)

               returnA -< ( Cout { coSel = sel
                                 , coTerm = term
                                 , coPaused = paused
                                 , coExns = exns
                                 , coSigs = sigs
                                 }
                          , d )
    in ( Sout { soPauses = soPauses then_s || soPauses else_s
              , soEmits  = emittedSigs
              , soThrows = thrownExns
              }
       , dyn )

-------------------------------------------------------------------
-- Exceptions.
-------------------------------------------------------------------

newtype Exception s = Exception ExnID

-- | Allocate a scoped local 'Exception'.
catchE :: (ArrowComb (~>), ArrowLoop (~>))
       => (forall s. Exception s -> (E (~>) c d))
       -> E (~>) c d
catchE f =
  E $ \sin ->
    let exns = siExns sin
        eid  = SeqA.length exns
        exn  = Exception eid

        l  = siLevel sin
        sin' = sin{ siExns = exns SeqA.|> l
                  , siLevel = l }

        (f_s, f_d) = unE (f exn) sin'
        f_s' = f_s{soThrows = eid `Set.delete` soThrows f_s}

        err = error $ "FIXME catchE is screwed, exn not in cout: " ++ show eid

        dyn = note ("catchE_" ++ show (unExnID eid)) $
          proc (cin, c) ->
            do rec kill <- SeqA.disjoin l -< ( ciKill cin
                                             , Map.findWithDefault err eid (coExns f_cout))
                   (f_cout, d) <- f_d -< (cin{ciKill = kill}, c)
               term <- SeqA.disjoin l -< ( coTerm f_cout
                                         , Map.findWithDefault err eid (coExns f_cout) )
               returnA -< ( f_cout { coTerm = term
                                   , coExns = eid `Map.delete` coExns f_cout -- FIXME verify
                                   }
                          , d )

    in if eid `Set.member` soThrows f_s
         then (f_s', dyn)
         else (f_s, f_d) -- Exception is unused.

-- | Throw an 'Exception'.
throwE :: ArrowComb (~>)
       => Exception s -> E (~>) v v
throwE (Exception eid) =
  E $ \sin ->
    let
        dyn = note ("throwE_" ++ show (unExnID eid)) $
          proc (cin, c) ->
            do cFalse <- falseA -< ()
               returnA -< ( Cout { coSel = cFalse
                                 , coTerm = SeqA.replicate (siLevel sin) cFalse
                                 , coExns = Map.singleton eid (ciGo cin)
                                 }
                          , c )
    in ( Sout { soPauses = False
              , soEmits = Set.empty
              , soThrows = Set.singleton eid
              }
       , dyn )

-------------------------------------------------------------------
-- Pre-emption (abort/when, previously do/watching (>>)).
-------------------------------------------------------------------

-- FIXME add a variant taking a B (~>).

abortE :: ArrowComb (~>)
       => Signal s -> E (~>) c d -> E (~>) c d
abortE (Signal sid) f =
  E $ \sin ->
    let l = siLevel sin
        sl = siSigs sin `SeqA.index` sid

        (f_s, f_d) = unE f sin

        dyn = note "abortE" $
          proc (cin, c) ->
            do let sigBit = (ciSigs cin `SeqA.index` sid) `SeqA.index` sl
               res <- andA <<< second notA -< (ciRes cin, sigBit)
               (cout, d) <- f_d -< (cin{ ciRes = res }, c)
               terml <- orA <<< second andA -< ( coTerm cout `SeqA.index` l
                                              , (res, sigBit) )
               let term = SeqA.update (coTerm cout) l terml
               returnA -< ( cout{coTerm = term}
                          , d )
    in (f_s, dyn) -- FIXME verify

-------------------------------------------------------------------
-- Debugging.
-------------------------------------------------------------------

printEnv :: (ArrowComb (~>), Show (B (~>)), Show b)
         => String -> E (~>) b b
printEnv str =
  E $ \_sin ->
      ( Sout { soPauses = False
             , soEmits = Set.empty
             , soThrows = Set.empty
             }
      , proc (cin, c) ->
          do cFalse <- falseA -< ()
             let cout = Cout { coSel = cFalse
                             , coTerm = ciGo cin }
             returnA -< ( trace (str ++ show cin) cout
                        , trace (str ++ show c) c
                        )
      )

-- | FIXME duplicates the underlying probeA logic, so the label is not
-- unique.
probeE :: ArrowProbe (~>) v => String -> E (~>) v v
probeE = lift . probeA

----------------------------------------
-- Non-determinism
-- We need to implement these in the kernel as lifting nondetC
-- makes independent choices at each level.
-- FIXME FIXME repair
----------------------------------------

-- | Non-deterministically choose between two 'E' computations.
nondetE = ifE (arr (const ()) >>> nondetAC falseA trueA)

-- | \"Fairly\" non-deterministically choose between two 'E'
-- computations.
nondetFairE = ifE (arr (const ()) >>> nondetFairAC falseA trueA)

{-

Requires -XUndecidableInstances:

instance (ArrowComb (~>), ArrowMux (~>) v, NonDet (~>) (B (~>)))
           => NonDet (E (~>)) v where
    nondetC = nondetE
    nondetFairC = nondetFairE

This is spurious: the B (~>) reduces and ~> vanishes - but perhaps
that is not generally true.

-}

-------------------------------------------------------------------
-- Esterel top-level.
-------------------------------------------------------------------

-- | FIXME provide a full interface + this convenience API.
-- FIXME outputs 'coTerm' which is true in the first instant the
-- circuit terminates and false thereafter. Want latching behaviour?
-- No, could imagine a reset.
runE :: (ArrowComb (~>), ArrowDelay (~>) (B (~>)), ArrowInit (~>))
     => E (~>) c d -> (c ~> (B (~>), d))
runE f =
  let sin = Sin { siExns = SeqA.empty
                , siSigs = SeqA.empty
                , siLevel = minBound
                }

      (_f_s, f_d) = unE f sin
  in note "runE" $
    proc c ->
      do boot <- isInitialState -< ()
         cFalse <- falseA -< ()
         cTrue <- trueA -< ()
         let cin = Cin { ciGo = SeqA.singleton boot
                       , ciRes = cTrue
                       , ciSusp = cFalse
                       , ciKill = SeqA.singleton cFalse
                       , ciSigs = SeqA.empty
                       }
         (cout, d) <- f_d -< (cin, SeqA.singleton c)
         returnA -< ( coTerm cout `SeqA.index` minBound
                    , d `SeqA.index` minBound )

{-

-------------------------------------------------------------------
-- Suspend.
-------------------------------------------------------------------

-- | Suspend on a boolean signal.
-- FIXME semantics.
-- FIXME verify acyclic.
suspendE :: (ArrowComb (~>), ArrowLoop (~>))
         => E (~>) gin gout
         -> E (~>) (gin, B (~>)) gout
suspendE f =
  MkE $ \s e ->
    let
      arrowF = unE f s e
      arrow =
        proc (cin, (gin, cond)) ->
          do rec t0 <- andA -< (sel', eciRes cin)
                 res' <- andA <<< second notA -< (t0, cond)
                 t1   <- andA -< (t0, cond)
                 susp' <- orA -< (eciSusp cin, t1)
                 let cin' = cin{ eciRes = res', eciSusp = susp' }
                 (cout@(MkECout { ecoSel = sel'}), gout)
                     <- arrowF -< (cin', gin)
             paused' <- orA -< (ecoPaused cout, t1)
             returnA -< (cout { ecoPaused = paused' }, gout)
    in arrow

-------------------------------------------------------------------
-- Debugging.
-------------------------------------------------------------------


-}
