{- CTL counter examples, following /Model Checking/ E. Clarke, O. Grumberg, D. Peled (2000).
 - Copyright   :  (C)opyright 2006, 2009-2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -
 - The tech report has more details:
 -   CMU-CS-94-204  "Efficient Generation of Counterexamples and Witnesses
 -                  in Symbolic Model Checking"
 -   E. Clarke, O. Grumberg, K. McMillan, X. Zhao. (1994)
 -}
module ADHOC.ModelChecker.CounterExamples
    ( Spec, sOK, sFail, mcce
    , showCounterExample
    , showWitness
    , showStates
    , showFailingStates
    ) where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude hiding ( id, (.) )
import Control.Monad ( foldM )

-- import Data.Map ( Map )
import qualified Data.Map as Map

import Text.PrettyPrint as PP hiding ( Mode )
-- import qualified Text.PrettyPrint as PP

import ADHOC.Basis
import ADHOC.Model

import ADHOC.ModelChecker.CTL as CTL

-------------------------------------------------------------------

data Mode = CounterExample | Witness

instance Show Mode where
  show c =
    case c of
      CounterExample -> "[CE]"
      Witness -> "[W]"

switchCommitment :: Mode -> Mode
switchCommitment CounterExample = Witness
switchCommitment Witness = CounterExample

-- | FIXME tidy this up, use the pretty printer
outputRewriteCE :: Show b => Mode -> String -> CTL b -> CTL b -> IO ()
outputRewriteCE _commitment _op _f _f1 = return ()
-- outputRewriteCE commitment op f f1 =
--   do putStrLn $ show commitment ++ " rewriting[" ++ op ++ "]: " ++ show f
--      putStrLn $ "   => " ++ show f1

-- | Print out a state in terms of the probes and observations.
showState :: CTLModel b -> b -> IO ()
showState ctlM s = putStrLn $ show doc
  where
    -- FIXME HACK: Omit the probes that come out false.
    rProbe (probeID, (_, obsRenderFn)) =
      text (probeID ++ ":") <+> renderFn obsRenderFn s
{-
      let r = renderFn obsRenderFn s
       in case show r of
        "F" -> PP.empty
        _ -> text (probeID ++ ":") <+> r
-}

    probes = hsep $ map rProbe $ Map.toList (mProbes (ctlModel ctlM))

    -- FIXME hang?
    doc = probes -- text "State:" <+> probes

-- | Print out a set of states.
--
-- FIXME Output a count of the number of paths through the BDD - CUDD
-- has a function, but not hard to implement anyway.
showStates :: (Boolean b, Eq b) => CTLModel b -> b -> IO ()
showStates ctlM s = mapObsM s obs f
  where
    -- FIXME this might be doing too much splitting.
    obs = concatMap fst (Map.elems (mProbes (ctlModel ctlM)))
    f (ss, _) = showState ctlM ss

-------------------------------------------------------------------

type Spec b = (String, Bool, CTL b)

sOK :: String -> CTL b -> Spec b
sOK fid f = (fid, True, f)

sFail :: String -> CTL b -> Spec b
sFail fid f = (fid, False, f)

mcce :: (BDDOps b, Show b) => CTLModel b -> [Spec b] -> IO Bool
mcce ctlM specs =
  do passes <- foldM chk (0::Int) specs
     putStrLn $ "Passed " ++ show passes ++ " of " ++ show (length specs)
     return (passes == length specs)
  where
    chk i (fid, ok, f) =
      do putStr $ fid ++ "... "
         case CTL.mc ctlM f of
           CTLok
             | ok -> putStrLn "passed" >> (return $! (i + 1))
             | otherwise ->
                 do putStrLn $ "\n*** Succeeded when it should fail"
                    case CTL.mc ctlM (neg f) of
                      CTLok -> error $ "CounterExamples.mcce: inconsistent!"
                      CTLfailure ss0 -> ctlCE ctlM CounterExample ss0 (neg f)
                    return i
           CTLfailure ss0
             | ok ->
                 do putStrLn $ "*** Failure"
                    ctlCE ctlM CounterExample ss0 f
                    putStrLn ""
                    return i
             | otherwise -> putStrLn "(fails) passed" >> (return $! (i + 1))

-- | Find an arbitrary witness (a trace) that a formula is false.
showCounterExample :: (BDDOps b, Show b)
                   => CTLModel b -> CTL b -> IO ()
showCounterExample ctlM f =
  case CTL.mc ctlM f of
    CTLok -> putStrLn $  "*** formula holds in model: " ++ show f
    CTLfailure ss0 -> ctlCE ctlM CounterExample ss0 f

-- | Find an arbitrary witness (a trace) that a formula is true.
showWitness :: (BDDOps b, Show b)
            => CTLModel b -> CTL b -> IO ()
showWitness ctlM f =
  case CTL.mc ctlM (neg f) of
    CTLok -> putStrLn $ "*** formula does not hold in model: " ++ show f
    CTLfailure ss0 -> ctlCE ctlM Witness ss0 f

-- | Show the initial states where a 'CTL' formula fails.
showFailingStates :: (BDDOps b, Show b)
                  => CTLModel b -> CTL b -> IO ()
showFailingStates ctlM f =
  case CTL.mc ctlM f of
    CTLok -> putStrLn "*** no failing states."
    CTLfailure s -> showStates ctlM s

-- | Find a witness or counter example to @f@ in the model @ctlM@
-- starting in a state in @ss0@. Assumes that @f@ holds in @ss0@ if
-- asked for a 'Witness', or doesn't hold if asked for a
-- 'CounterExample'.
ctlCE :: (BDDOps b, Show b)
      => CTLModel b -> Mode -> b -> CTL b -> IO ()
ctlCE ctlM commitment ss0 f =
      case f of
        -- Done, trivially.
        CTLprop {} ->
          case commitment of
            Witness -> findEGWitness ctlM true ss0
            CounterExample -> findEGWitness ctlM true ss0

        -- Done, trivially.
        CTLprobe {} ->
          case commitment of
            Witness -> findEGWitness ctlM true ss0
            CounterExample -> findEGWitness ctlM true ss0

        f1 `CTLand` f2 ->
          case commitment of
            Witness ->
              do -- f is satisfiable in ss0, so either conjunct will do.
                 outputRewriteCE commitment "/\\" f f1
                 ctlCE ctlM commitment ss0 f1
            CounterExample -> -- FIXME I guess this is the user's turn, so to speak.
              case CTL.mc ctlM f1 of
                CTLok -> ctlCE ctlM commitment ss0 f2
                _     -> ctlCE ctlM commitment ss0 f1

        f1 `CTLor` f2 ->
          do let f' = neg (neg f1 /\ neg f2)
             outputRewriteCE commitment "\\/" f f'
             ctlCE ctlM commitment ss0 f'

        f1 `CTLxor` f2 ->
          case commitment of
            Witness        -> putStrLn $ "ctlCE failure: CTLxor Witness: " ++ show f
            CounterExample -> putStrLn $ "ctlCE failure: CTLxor CounterExample: " ++ show f

        f1 `CTLimplies` f2 ->
          do let f' = f2 \/ neg f1 -- FIXME we're typically more interested in the case where f2 is true than when f1 is false.
             outputRewriteCE commitment "-->" f f'
             ctlCE ctlM commitment ss0 f'

        f1 `CTLiff` f2 ->
          case commitment of
            Witness        -> putStrLn $ "ctlCE failure: CTLiff Witness: " ++ show f
            CounterExample -> putStrLn $ "ctlCE failure: CTLiff CounterExample: " ++ show f

        CTLneg f1 ->
          do outputRewriteCE commitment "neg -- switch commitment" f f1
             ctlCE ctlM (switchCommitment commitment) ss0 f1

      -- CTL

        CTLax f1 ->
          do let f' = neg $ CTLex $ neg f1
             outputRewriteCE commitment "AX" f f'
             ctlCE ctlM commitment ss0 f'
        CTLex f1 ->
          case commitment of
            Witness        -> findEXWitness ctlM ss0 f1
            CounterExample -> putStrLn $ "ctlCE failure: CTLex CounterExample: " ++ show f

        CTLaf f1 ->
          do let f' = neg $ CTLeg $ neg f1
             outputRewriteCE commitment "AF" f f'
             ctlCE ctlM commitment ss0 f'
        CTLef f1 ->
          do let f' = true `CTLeu` f1
             outputRewriteCE commitment "EF" f f'
             ctlCE ctlM commitment ss0 f'

        CTLag f1 ->
          do let f' = neg $ true `CTLeu` neg f1
             outputRewriteCE commitment "AG" f f'
             ctlCE ctlM commitment ss0 f'
        CTLeg f1 ->
          case commitment of
            Witness        -> findEGWitness ctlM f1 ss0
            CounterExample -> putStrLn $ "ctlCE failure: CTLeg CounterExample: " ++ show f

        f1 `CTLau` f2 ->
          do let f' = neg (neg f2 `CTLeu` (neg f1 /\ neg f2))
                         /\ neg (CTLeg (neg f2))
             outputRewriteCE commitment "AU" f f'
             ctlCE ctlM commitment ss0 f'
        f1 `CTLeu` f2 ->
          case commitment of
            Witness ->
              do let f1e = CTL.sat ctlM f1
                     f2e = CTL.sat ctlM f2
                 findEUWitness ctlM False ss0 f1e f2e >>= findEGWitness ctlM true
            CounterExample -> putStrLn $ "ctlCE failure: CTLeu CounterExample: " ++ show f

-------------------------------------------------------------------

-- | Find a witness for a formula of the form "EX f", starting at state 's'.
findEXWitness :: (BDDOps b, Show b)
              => CTLModel b -> b -> CTL b -> IO ()
findEXWitness ctlM ss0 f0 =
    assert (ss0 /\ exf /= false) $
           do showState ctlM s0
              ctlCE ctlM Witness (forwardOneStep ctlM s0) f0
    where
      s0 = chooseState ctlM $ ss0 /\ exf
      f = CTL.sat ctlM f0
      exf = CTL.ex_sem ctlM f

-------------------------------------------------------------------

-- | Find a witness for a formula of the form "EG f", starting at state 's'.
-- Assumptions:
--   - there is at least one fairness constraint.
findEGWitness :: (BDDOps b, Show b)
              => CTLModel b -> CTL b -> b -> IO ()
findEGWitness ctlM f0 ss0 = assert (ss0 /\ egf /= false) $
  do -- putStrLn $ ">> findEGWitness" -- : " ++ show ss0 ++ " / " ++ show f0
     _ <- findSCC ss0
     return ()
  where
      f = CTL.sat ctlM f0
      egf = CTL.eg_sem ctlM f

      -- Traverse the state space until we find an SCC we like.
      findSCC ss = do mapM_ (showState ctlM) prefix
                      if scc /= false
                        then do putStrLn ">> loop <<"
                                findEUWitness ctlM True ss1 f scc
                        else findSCC ss1
          where (prefix, ss1, scc) = findQi ss

      fairnessConstraints = maybe [true] ctlFairConstraints (ctlMFair ctlM)
      allqs = [ fUegfAh $ egf /\ hk
                | hk <- fairnessConstraints ]

      -- This is the E[f U ((EG f) /\ h)] fixpoint computation, unfolded.
      fUegfAh ss = ss : fUegfAh (ss \/ (f /\ CTL.ufex ctlM ss))

      -- | FIXME comment
      findQi ss = foldr eachH ([], ss, true) allqs
          where
            -- Non-false iff there's a path from a successor of s back to s,
            -- keeping f true all the way.
            loop' = CTL.ufex ctlM $ CTL.ufeu ctlM f ss

            eachH (qi:qs) orig@(prefix, ss1, firstState)
                | firstState == false = orig -- trace (">> eachH bailing 1") $ orig
                | sqi /= false = -- trace (">> eachH bailing 2: " ++ show slsqi) $
                                 ( slsqi : prefix
                                 , forwardOneStep ctlM slsqi
                                 , lsqi )
                | otherwise = -- trace (">> eachH recur:" ++ show p') $
                              ( p' : suffix
                              , forwardOneStep ctlM p'
                              , firstState' )
                where sqi = ss1 /\ qi
                      lsqi = loop' /\ sqi
                      maybeLSQI = if lsqi == false then sqi else lsqi
                      slsqi = chooseState ctlM maybeLSQI

                      (suffix, p, firstState') = eachH qs orig
                      pqi = p /\ qi
                      lpqi = loop' /\ pqi
                      maybeLPQI = if lpqi == false then pqi else lpqi
                      p' = chooseState ctlM $ maybeLPQI

-------------------------------------------------------------------

-- | Find a witness for a formula of the form "f EU g", starting at state 'ss0'.
-- Assumes that such a witness exists; if not, it doesn't terminate.
-- Returns the final state on the path.
findEUWitness :: forall b. (BDDOps b, Show b)
              => CTLModel b
              -> Bool -- display the final state or not?
              -> b -> b -> b -> IO b
findEUWitness ctlM displayFinalState ss0 f g =
  do -- putStrLn ">> findEUWitness"
     mapM_ (showState ctlM) ((if displayFinalState then id else init) path)
     return (last path)
  where
    path = forwardR (backwardR g [])

    ss0f = ss0 /\ f
    tr = mTr (ctlModel ctlM)
    groupC = ctlGroupC ctlM
    groupS = ctlGroupS ctlM
    subCforS = ctlSubCforS ctlM
    subSforC = ctlSubSforC ctlM

    backwardR :: b -> [b] -> [b]
    backwardR ss p
      | ssInit /= false = ssInit : p
      | otherwise = backwardR preds (ss : p)
      where ssInit = ss0f /\ ss
            preds = f /\ rel_product groupS (subSforC ss) tr

    forwardR :: [b] -> [b]
    forwardR [ss] = [chooseState ctlM ss]
    forwardR (ss:ss':p) =
      let sss = chooseState ctlM ss
       in sss : forwardR ((ss' /\ subCforS (rel_product groupC sss tr)) : p)
