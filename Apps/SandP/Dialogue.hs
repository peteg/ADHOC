{-# LANGUAGE Arrows, FlexibleContexts, ScopedTypeVariables, TypeOperators #-}
{- A simple interpretation of a dialogue.
 - Copyright   :  (C)opyright 2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -}
module Dialogue where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude hiding ( (.), id )
import Control.Monad ( foldM, liftM, liftM2 )

import ADHOC
import ADHOC.Data.Arithmetic

-------------------------------------------------------------------
-- Dialogues.
-------------------------------------------------------------------

{-

The dialogue involves the use of past time, which @KF@ does not
support. Therefore we define a new logic just for this problem.

In general past-time operators need non-local transformations, e.g. we
need to add a proposition for each previous-instant propositional
subformula.

However this language can be handled locally to an agent:

-}

data KFP =
    KFPfalse
  | KFPtrue
  | KFP `KFPand` KFP
  | KFPneg KFP
  | KFPpre KF -- ^ "in the previous instant..."
  | KFPnow KF -- ^ "in this instant..."
  deriving (Eq, Show)

pre, now :: KF -> KFP
pre = KFPpre
now = KFPnow

instance Boolean KFP where
  false = KFPfalse
  true  = KFPtrue
  (/\) = KFPand
  neg = KFPneg

{-

A dialogue is amongst several agents, with some agent making some
broadcast announcement at each step.

FIXME the dialogue needs to be a sized list so we can create a state
counter for it.

-}

data Announcement = AgentID :> KFP

infix 0 :>

type Dialogue w = SizedList w Announcement

{-

We translate a @KFP@ formula into an arrow. We memoise knowledge tests
to reduce the number of automata we construct.

-}

-- | Add a basic knowledge test to the environment.
kt :: Arrow (~>) => KF -> StateM [KF] ([B (~>)] ~> B (~>))
kt f0 = StateM (findKT 0)
  where
    findKT :: Arrow (~>) => Int -> [KF] -> ([B (~>)] ~> B (~>), [KF])
    findKT n [] = (arr (\xs -> xs !! n), [f0])
    findKT n ffs@(f : fs)
      | f0 == f   = (arr (\xs -> xs !! n), ffs)
      | otherwise = second (f:) (findKT (n+1) fs)
        -- case findKT (n+1) fs of
        --   (darr, fs') -> (darr, f : fs')


kfp2kp :: (ArrowComb (~>), ArrowDelay (~>) (B (~>)))
       => KFP -> StateM [KF] ([B (~>)] ~> B (~>))
kfp2kp = go
  where
    go f = case f of
      KFPfalse -> return falseA
      KFPtrue -> return trueA
      f1 `KFPand` f2 -> liftM2 andAC (go f1) (go f2)
      KFPneg f1 -> fmap notAC (go f1)
      KFPnow (KFneg f1) -> liftM notAC (go (now f1))
      KFPnow f1 -> kt f1
      KFPpre (KFneg f1) -> liftM notAC (go (pre f1))
      KFPpre f1 -> liftM (delayAC falseA) (kt f1)

{-

We treat each agent's role in the dialogue separately.

-}

dialogueForAgent aid (d :: Dialogue dlen) = proc (_iobs, (s, _acts)) ->
    do kts <- kt -< ()
       darr -< (s, kts)
  where
    kt = foldr (liftA2 (:) . kTest) (arr (const [])) kts

    (darr, kts) = runStateM encD []
    encD = foldM encS trueA (zip [ 0 .. ] (unSizedListA d)) -- Count dialogue steps from 0

    encS darr (i, aid' :> statement) =
      do sarr <- if aid == aid' then kfp2kp statement else return trueA
         return $ proc (s, kts) ->
           (| muxAC ( (returnA -< s) `eqAC` (constNatA (undefined :: dlen) i -< ()) )
                (sarr -< kts)
                (darr -< (s, kts)) |)

{-

FIXME describe.

-}

{-
runDialogue :: forall (~>) dlen ienv iobs size.
               (ArrowComb (~>),
                ArrowDelay (~>) (B (~>)),
                ArrowDelay (~>) (SizedList size (B (~>))),
                ArrowDelay (~>) (Nat dlen (~>)),
                ArrowLoop (~>),
                ArrowMux (~>) (B (~>)),
                ArrowMux (~>) (Nat dlen (~>)),
                ArrowNum (~>) (Nat dlen (~>)),
                ArrowOrd (~>) (Nat dlen (~>)),
                Broadcast (~>) iobs (Nat dlen (~>), SizedList size (B (~>))),
                KBPTest (~>),
                Card size, Card dlen)
            => SizedList size (AgentID, ienv ~> iobs)
            -> Dialogue dlen
            -> (ienv ~> SizedList size (B (~>)))
-}
runDialogue agents (d :: Dialogue dlen) = proc ienv ->
  do rec dState <- (| delayAC (constNatA (undefined :: dlen) 0 -< ())
                              ( (constNatA (undefined :: dlen) (dlen - 1) -< ())
                                  `minAC` (incA -< dState) ) |)
     rec acts <- (| delayAC (replicateSL <<< trueA -< ())
                            (| (broadcast aars)
                                  (returnA -< ienv)
                                  (returnA -< (dState, acts)) |) |)
     returnA -< acts
  where
    dlen = c2num (undefined :: dlen)
    aars = mapSL (\(aid, iarr) -> (aid, iarr, dialogueForAgent aid d)) agents
