{- Explicit-state automata.
 - Copyright   :  (C)opyright 2006, 2009-2011 peteg42 at gmail dot com
 - License     :  BSD (see LICENCE for details)

Note this is all horribly mutable and hence single-threaded.

-}
module ADHOC.Knowledge.ExplicitStateAutomata
       (
         Automaton
       , Automata
       , Hashable(..)
       , bmAgentID
       , bmKF
       , bmObs, bmRenderObs
       , bmOutBit
       , bmOutBit'

       , Synth, Minimize(..)

       , mk
       , finished
       , addInitialTransition
       , addTransition
       , minimize, bisim, stamina

       , toModel
       , automata2model

       , dump

       , dot
       , kiss2
       ) where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude hiding ( id, (.) )

import Control.Monad	( foldM, when )

import Data.List	( groupBy, sortBy )
import Data.IORef

-- Hashtables have the advantage that they support arbitrary key
-- types. Judy arrays would be nice but generally our keys are two
-- words, not one.
import Data.HashTable	( HashTable )
import qualified Data.HashTable as HT
import Data.Int         ( Int32 )
import qualified Data.Bits as B ( rotate, xor )

import Data.IntMap	( IntMap )
import qualified Data.IntMap as IntMap

import Data.DFA         ( DFA, State, Label )
import qualified Data.DFA as DFA
import qualified Data.DFA.DOT as DOT
import qualified Data.DFA.KISS2 as KISS2
import qualified Data.DFA.STAMINA as STAMINA

import ADHOC.Basis
import ADHOC.Constructivity ( CArrow )
import ADHOC.Model	( KF(..), Model(..), RenderFn(..) )

import ADHOC.Data.ArithmeticCircuits ( toNatBC )

import ADHOC.Knowledge.Hash

-------------------------------------------------------------------

instance Hashable BDD where
  hash = hashWord32 . fromInteger . toInteger . get_bdd_ptr

-- We don't care about the inverse state map, as after minimization it
-- is a many-to-one relation. Would need to support it in hdfa.

-- Think about garbage collection: the observation might be
-- huge. The state map is useless.
-- Everything else is needed or small ??

data Automaton b l s =
    Automaton
    { bmAgentID :: AgentID
    , bmObs :: [b] -- ^ Agent observation
    , bmRenderObs :: RenderFn b -- ^ Function to render the observation

    , bmLabelMap :: HashTable l Label
    , bmLabelInvMap :: IORef (IntMap l) -- ^ Maps 'Label' to l
    , bmNumLabels :: IORef Label
    , bmNumStates :: IORef State
    , bmStateMap :: HashTable s State

      -- This stuff is per-Kcond.
    , bmKF :: KF
    , bmOutBit :: b -- ^ Current-state out bit for the knowledge automaton
    , bmOutBit' :: b -- ^ Next-state out bit for the knowledge automaton
    , bmDFA :: DFA
    }

type Automata b l s = [Automaton b l s]

-- | Minimization options
data Minimize = MinNone | MinBisim | MinSTAMINA

-- | The type of knowledge synthesis functions.
type Synth b s c = Minimize -> CArrow () c -> Maybe (Automata b b s, Model b, c)

mk :: (Eq l, Eq s, Hashable l, Hashable s)
   => Model b -> (AgentID, (KF, (b, b))) -> IO (Automaton b l s)
mk m (aid, (kf, (outBit, outBit'))) =
  do dfa <- DFA.initialize False 0 -- Tell hDFA to be quiet, 0 is the initial state.
     lm  <- HT.new (==) (asInt32 . hash)
     lim <- newIORef IntMap.empty
     sm  <- HT.new (==) (asInt32 . hash)
     lc  <- newIORef 0
     sc  <- newIORef 1 -- the initial state is 0.
     return Automaton { bmAgentID = aid
                      , bmObs = obs
                      , bmRenderObs = renderObs
                      , bmKF = kf
                      , bmOutBit = outBit
                      , bmOutBit' = outBit'
                      , bmLabelMap = lm
                      , bmLabelInvMap = lim
                      , bmNumLabels = lc
                      , bmNumStates = sc
                      , bmStateMap = sm
                      , bmDFA = dfa
                      }
  where
    Just (obs, renderObs) = lookup aid (mAgents m)

finished :: Automaton b l s -> IO ()
finished = DFA.finished . bmDFA

addLabel :: Ord l => Automaton b l s -> l -> IO (Bool, Label)
addLabel auto l =
  do mlid <- HT.lookup (bmLabelMap auto) l
     case mlid of
       Just lid -> return (False, lid)
       Nothing  ->
         do lid <- readIORef (bmNumLabels auto)
            writeIORef (bmNumLabels auto) $! (succ $! lid)
            -- putStrLn $ "new lid: " ++ show lid
            HT.insert (bmLabelMap auto) l lid
            lim <- readIORef (bmLabelInvMap auto)
            writeIORef (bmLabelInvMap auto) $! IntMap.insert ((fromInteger . toInteger) lid) l lim
            return (True, lid)

-- | Add a state to the automaton. Returns the state identifier and
-- whether the state is new.
addState :: Ord s => Automaton b l s -> s -> IO (Bool, State)
addState auto s =
  do msid <- HT.lookup (bmStateMap auto) s
     case msid of
       Just sid -> return (False, sid)
       Nothing  ->
         do sid <- readIORef (bmNumStates auto)
            writeIORef (bmNumStates auto) $! (succ $! sid)
            -- putStrLn $ "new sid: " ++ show sid
            HT.insert (bmStateMap auto) s sid
            return (True, sid)

-- | Add an initial transition. Returns whether the state is new.
addInitialTransition :: (Ord l, Ord s) => Automaton b l s -> l -> s -> Bool -> IO Bool
addInitialTransition auto l t tb =
  do (tNew, tid) <- addState auto t
     (_, lid) <- addLabel auto l
     q0 <- DFA.getInitialState dfa
     DFA.addTransition dfa (q0, lid, tid)
     when tb $ DFA.setFinal dfa tid
     return tNew
  where dfa = bmDFA auto

-- | Add a transition to @auto@ from @s@ to @t@, labelled with
-- @l@. Set the satisfiability bit on @t@ if to @tb@.
--
-- Returns @True@ if @t@ is a new state, and @False@ otherwise.
addTransition :: (Ord l, Ord s) => Automaton b l s -> s -> l -> s -> Bool -> IO Bool
addTransition auto s l t tb =
  do (_, sid) <- addState auto s
     (_, lid) <- addLabel auto l
     (tNew, tid) <- addState auto t
     DFA.addTransition dfa (sid, lid, tid)
     when tb $ DFA.setFinal dfa tid
     return tNew
  where dfa = bmDFA auto

----------------------------------------

-- | Minimize the DFA in-place.
minimize :: Minimize -> Automaton b l s -> IO (Automaton b l s)
minimize minType auto =
  case minType of
    MinNone -> return auto
    MinBisim -> bisim auto
    MinSTAMINA -> bisim auto >>= stamina

-- FIXME toss debug
bisim :: Automaton b l s -> IO (Automaton b l s)
bisim auto =
  do putStrLn "ADHOC.Knowledge.ExplicitStateAutomata.minimize"
     DFA.minimize (bmDFA auto) True
     return auto

-- FIXME path to the binary.
stamina_path :: FilePath
stamina_path = "/Users/peteg/msc/hacking/sis/sis-1.2/stamina/bin/stamina"

-- | Minimize the DFA using STAMINA. This creates a new automaton.
stamina :: Automaton b l s -> IO (Automaton b l s)
stamina auto =
  do putStrLn "ADHOC.Knowledge.ExplicitStateAutomata.stamina"
     dfa' <- STAMINA.minimize stamina_path (bmDFA auto)
     return auto{bmDFA = dfa'}

----------------------------------------

-- | Convert the automaton back into BDDs.
toModel :: (Boolean b, BooleanVariable b, Substitution b, Show b)
        => Model b -> (Integer, Automaton b b s) -> IO (Model b)
toModel m (auto_uniquifier, bm) =
  do let dfa = bmDFA bm
         outBit = bmOutBit bm
         outBit' = bmOutBit' bm
     -- FIXME
     -- (HT.toList (bmStateMap bm) >>= \x -> putStrLn $ "StateMap # keys: " ++ show (length x))
     -- (HT.longestChain (bmStateMap bm) >>= \x -> putStrLn $ "StateMap longest chain: " ++ show (length x))
     -- (HT.longestChain (bmLabelMap bm) >>= \x -> putStrLn $ "LabelMap longest chain: " ++ show (length x))
     numStates <- DFA.numStates dfa
     putStrLn $ "Number of dfa states: " ++ show numStates
     let
       -- Number of bits required.
       width :: Integer
       width  = ceiling $ (logBase 2 (fromIntegral (toInteger numStates)) :: Double)

       -- Uniquify the automata's state bits. This is a bit brittle.
       vname i = "%Syn_" ++ bmAgentID bm ++ "_" ++ show auto_uniquifier ++ "_" ++ show i
       props = [ bvars $ [vname i, prime (vname i)]
                           ++ [ vname i ++ "_" ++ show j | j <- [ 1 .. length (mTmpVars m) ] ]
               | i <- [ width - 1, width - 2 .. 0 ] ]

       (newStateVars, newStateVars', tmpVars') = futz props
       futz = foldr (\(v:v':ts) (vs, vs', tss) -> (v:vs, v':vs', zipWith (:) ts tss))
                    ([], [], mTmpVars m)

       -- Subtlety: the observation is made on the successor states.
       subSforC = rename (mkSubst (zip (mStateVars m) (mStateVars' m)))

       eqB x y = conjoin (zipWith (<->) x y)

       fTrans q0 lim (sid, lid, tid, kfHolds) (ei, et) = ei `seq` et `seq`
         do -- putStrLn $ "fTrans: " ++ show (sid, lid, tid, kfHolds)
            when (tid == q0) $ putStrLn $ "fTrans: transition to q0: " ++ show (sid, lid, tid)
            return $ case (fromInteger . toInteger) lid `IntMap.lookup` lim of
              Nothing  -> error $ "fTrans, obs with lid " ++ show lid ++ " not possible ??"
              Just obs ->
                let ei' | sid == q0
                            = ei /\ (obs --> ((if kfHolds then outBit else neg outBit)
                                        /\ eqB (toNatBC width tid) newStateVars))
                        | otherwise = ei
                    et' = et /\ ((eqB (toNatBC width sid) newStateVars /\ subSforC obs)
                                   --> ((if kfHolds then outBit' else neg outBit')
                                        /\ eqB (toNatBC width tid) newStateVars'))
                 in (ei', et')

     q0 <- DFA.getInitialState dfa
     lim <- readIORef (bmLabelInvMap bm)
     putStrLn $ "q0: " ++ show q0
     (initStates', tr') <- DFA.foldTransitions dfa (fTrans q0 lim) (mInitStates m, mTr m)

     let m' = m { mInitStates = initStates'
                , mTr = tr'
                , mStateVars = newStateVars ++ mStateVars m
                , mStateVars' = newStateVars' ++ mStateVars' m
                , mTmpVars = tmpVars'
                , mKconds = []
                }

     m' `seq` return m'

-- | Convert automata back to BDDs.
automata2model :: (Boolean b, BooleanVariable b, Substitution b, Show b)
               => Model b -> Automata b b s
               -> IO (Model b)
automata2model m = foldM toModel m . zip [ 1 .. ]

----------------------------------------

-- | FIXME dump automata
dump :: String -> Automata b l s -> IO ()
dump prefix = mapM_ go . zip [ 0::Integer .. ]
  where
    go (uniquifier, auto) = DFA.dumpToFile (bmDFA auto) (prefix ++ show uniquifier)

-- | Write the automata in dot (graphviz) format to files.
--
-- The filenames are @Kauto_/agent_id/_uniquifier.dot@.
--
-- FIXME maybe also include the synthesis method.
dot :: Automata b b s -> IO ()
dot = mapM_ go . concatMap (zip [ 0 :: Integer .. ]) . groupBy ((==) `on` bmAgentID) . sortBy (compare `on` bmAgentID)
  where
    go (uniquifier, auto) =
      do lim <- readIORef (bmLabelInvMap auto)
         let fn = "Kauto_" ++ bmAgentID auto ++ "_" ++ show uniquifier ++ ".dot"
             labelFn :: Label -> String
             labelFn lid =
                 show (renderFn (bmRenderObs auto) (IntMap.findWithDefault err ((fromInteger . toInteger) lid) lim))
               where err = error $ "ExplicitStateAutomata.dot: obs inv map broken: looking for " ++ show lid ++ " in " ++ show (IntMap.keys lim)
         DOT.writeToFile (bmDFA auto) fn labelFn

-- | Write the automata in kiss2 (Berkeley) format to files.
--
-- The filenames are @Kauto_/agent_id/_uniquifier.kiss2@.
--
-- FIXME maybe also include the synthesis method.
kiss2 :: Automata b b s -> IO ()
kiss2 = mapM_ go . concatMap (zip [ 0 :: Integer .. ]) . groupBy ((==) `on` bmAgentID) . sortBy (compare `on` bmAgentID)
  where
    go (uniquifier, auto) =
      do let fn = "Kauto_" ++ bmAgentID auto ++ "_" ++ show uniquifier ++ ".kiss2"
         KISS2.writeToFile (bmDFA auto) fn
