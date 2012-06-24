{-# LANGUAGE TypeFamilies, UndecidableInstances #-}
{- Netlist generator, following Ross Paterson.
 - Copyright   :  (C)opyright 2006, 2009-2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)

FIXME

Ranks: can we get the inputs and outputs to be at the extreme
positions?


-}
module ADHOC.NetList
    ( NetList
    , NodeID
    , inp, inpn, outp
    , mkNL
    , mkNL1
    , mkNL2

    , NodeAttr(..)
    , NodeShape(..)
    , WireAttr(..)

    , NLArrow
    , runNL_prim
    , runNL
    , runNLbits

    , nl2dot
    , dotNL
    , dotNLbits
    ) where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude hiding ( id, (.) )

import Control.Monad	( liftM2 )
import Data.List	( genericDrop, genericReplicate, genericTake )

import ADHOC.Circuits
import ADHOC.Generics
import ADHOC.Model
import ADHOC.NonDet
import ADHOC.Patterns	( mapA, mapAC )

-------------------------------------------------------------------
-- Netlists.
-------------------------------------------------------------------

-- Graph types.

-- | FIXME abstract NodeID
newtype NodeID = NodeID Int

instance Show NodeID where
  show (NodeID i) = show i

type NodeLabel = String

data NodeShape = Sbox | Scirc | Sparallelogram | Stext | Strapezoid | Striangle

instance Show NodeShape where
    show s = case s of
               Sbox           -> "box"
               Scirc          -> "oval"
               Sparallelogram -> "parallelogram"
               Stext          -> "plaintext"
               Strapezoid     -> "trapezium"
               Striangle      -> "triangle"

data NodeAttr
    = NodeAttr { nLabel :: !NodeLabel
               , nShape :: !NodeShape }
      deriving Show

-- | Labelled, clustered nodes.
data Nodes
    = NoNodes
    | Node { nID :: !NodeID, nAttrs :: !NodeAttr }
    | Nodes !Nodes !Nodes
    | SubNetList String !Nodes
      deriving Show

catNodes :: Nodes -> Nodes -> Nodes
catNodes NoNodes y = y
catNodes x NoNodes = x
catNodes x y       = Nodes x y

data WireAttr
    = NoWireAttrs
    | WireAttr { wLabel :: NodeLabel }
      deriving Show

-- | Descriptions of wires.
data Wire
    = Wire { wID :: !NodeID -- ^ Source of this wire
           , wAttrs :: WireAttr -- ^ Attributes
           }
      deriving Show

-- | Nameless inputs.
inp :: NodeID -> Wire
inp i = Wire { wID = i, wAttrs = NoWireAttrs }

-- | Named inputs.
inpn :: NodeLabel -> NodeID -> Wire
inpn l i = Wire { wID = i, wAttrs = WireAttr { wLabel = l } }

-- | Nameless outputs.
outp :: NodeID -> Wire
outp i = Wire { wID = i, wAttrs = NoWireAttrs }

instance StructureDest NodeID NodeID where
  destructure = (:[])

instance Structure NodeID NodeID where
  type SIwidth NodeID NodeID = One
  structure = sallocSM

-- | A node is related to its input wires.
type AssocList = [(NodeID, [Wire])]

-- | A netlist is a graph where the nodes have hierarchical structure.
type NetList = (Nodes, AssocList)

nlEmpty :: NetList
nlEmpty = (NoNodes, [])

nlAppend :: NetList -> NetList -> NetList
(ns0, al0) `nlAppend` (ns1, al1) = (ns0 `catNodes` ns1, al0 ++ al1)

nlSub :: String -> NetList -> NetList
nlSub str (ns, al) = (SubNetList str ns, al)

----------------------------------------
-- The NetList arrow.
----------------------------------------

-- | The net list 'Arrow': given a list of unique identifiers,
-- construct the net list. The @detail@ type tells us how much detail
-- to present, e.g. a high level or down to bits.
newtype NLArrow detail b c =
  NLArrow { runNLArrow :: b -> StateM [NodeID] (NetList, c) }

-- | Construct a node for an arbitrary fan-in gate.
mkNL :: (b -> (NodeAttr, [Wire])) -> NLArrow detail b NodeID
mkNL f = NLArrow $ \b ->
  do nodeID <- modifySM (\(nodeID : nodeIDs) -> (nodeID, nodeIDs))
     let (nA, inputs) = f b
     return ( ( Node{nID = nodeID, nAttrs = nA}
              , [(nodeID, inputs)] )
            , nodeID )

-- | Construct a node for a constant.
mkNLconst :: NodeAttr -> NLArrow detail b NodeID
mkNLconst nA = mkNL (\_ -> (nA, []))

-- | Construct a node for a single-input gate.
mkNL1 :: (NodeAttr, WireAttr) -> NLArrow detail NodeID NodeID
mkNL1 (nA, wA) = mkNL $ \i -> (nA, [Wire { wID = i, wAttrs = wA }])

-- | Construct a node for a two-input gate.
mkNL2 :: (NodeAttr, (WireAttr, WireAttr))
      -> NLArrow detail (NodeID, NodeID) NodeID
mkNL2 (nA, (wA1, wA2)) = mkNL $ \(i1, i2) ->
      (nA, [ Wire { wID = i1, wAttrs = wA1 }
           , Wire { wID = i2, wAttrs = wA2 } ])

-------------------------------------------------------------------
-- Arrow instances.
-------------------------------------------------------------------

instance Category (NLArrow detail) where
  id = NLArrow $ arr $ \b -> return (nlEmpty, b)
  NLArrow g . NLArrow f = NLArrow $ \b ->
    do (nlf, c) <- f b
       (nlg, d) <- g c
       return (nlf `nlAppend` nlg, d)

instance Arrow (NLArrow detail) where
  arr f = NLArrow $ \b -> return (nlEmpty, f b)
  first (NLArrow f) = NLArrow $ \(b, d) ->
    do (nl, c) <- f b
       return (nl, (c, d))

instance ArrowLoop (NLArrow detail) where
  loop f = NLArrow $ \b ->
    do (nl, (c, _d)) <- recSM (\ ~(_nl, ~(_c, d)) -> runNLArrow f (b, d))
       return (nl, c)

instance ArrowComb (NLArrow detail) where
  type B (NLArrow detail) = NodeID

  falseA = mkNLconst (NodeAttr {nLabel = "falseA", nShape = Sbox})
  trueA  = mkNLconst (NodeAttr {nLabel = "trueA", nShape = Sbox})

  andA = mkNL2 (NodeAttr {nLabel = "andA", nShape = Scirc}, (NoWireAttrs, NoWireAttrs))
  notA = mkNL1 (NodeAttr {nLabel = "notA", nShape = Striangle}, NoWireAttrs)

  nandA = mkNL2 (NodeAttr {nLabel = "nandA", nShape = Scirc}, (NoWireAttrs, NoWireAttrs))

  orA = mkNL2 (NodeAttr {nLabel = "orA", nShape = Scirc}, (NoWireAttrs, NoWireAttrs))

  xorA = mkNL2 (NodeAttr {nLabel = "xorA", nShape = Scirc}, (NoWireAttrs, NoWireAttrs))

  iffA = mkNL2 (NodeAttr {nLabel = "iffA", nShape = Scirc}, (NoWireAttrs, NoWireAttrs))

  impA = mkNL2 (NodeAttr {nLabel = "impA", nShape = Scirc}, (NoWireAttrs, NoWireAttrs))

  -- FIXME: this doesn't work on pure circuits, e.g. id (there's no subgraph to hang on to).
  note label (NLArrow f) = NLArrow $ \b ->
    do (nl, c) <- f b
       return (nlSub label nl, c)

-- FIXME we'd probably like to know what type 'v' we're zeroing.
instance Zero (NLArrow detail) NodeID where
  zeroA = mkNLconst (NodeAttr {nLabel = "zeroA", nShape = Sbox})

----------------------------------------

-- This does not track bit slices but looks like it might.
instance Structure NodeID v => ArrowMux (NLArrow detail) v where
  muxA = proc (sel, (a, b)) ->
      arr (fst . runStateM structure) <<< mkMux -< (sel, zip (destructure a) (destructure b))
    where
      width = c2num (undefined :: SIwidth NodeID v) :: Integer

      mkMux
        | width == 1 =
            mkNL (\(sel, [(tl, el)]) ->
                     (NodeAttr {nLabel = "mux", nShape = Strapezoid},
                      [ inpn "sel" sel, inpn "t" tl, inpn "f" el ]))
              >>> arr (:[])
        | otherwise = note "mux" $ proc (sel, asbs) ->
            (| (mapAC width) (\ab -> mkMux1 -< (sel, ab)) |) asbs

      mkMux1 = mkNL (\(sel, (tl, el)) ->
                       ( NodeAttr {nLabel = "", nShape = Strapezoid},
                         [ inpn "sel" sel, inpn "t" tl, inpn "e" el ] ))

instance Structure NodeID v => ArrowDelay (NLArrow detail) v where
  delayA = proc (v0, v1) -> mkDelay -< zip (destructure v0) (destructure v1)
    where
      width = c2num (undefined :: SIwidth NodeID v) :: Integer

      mkDelay
        | width == 1 =
            mkNL (\[(v0, v)] ->
                    ( NodeAttr {nLabel = "delay", nShape = Sbox},
                      [ inpn "init" v0, inpn "rec" v] ))
               >>> arr (fst . runStateM structure . (:[]))
        | otherwise = note "delay" $
            mapA width (mkNL (\(v0, v) ->
                    ( NodeAttr {nLabel = "", nShape = Sbox},
                      [ inpn "init" v0, inpn "rec" v] )))
               >>> arr (fst . runStateM structure)

instance ArrowCombLoop (NLArrow detail) r where
  combLoop = loop

instance Structure NodeID v => ArrowProbe (NLArrow detail) v where
  probeA str = arr destructure >>> mkProbe
    where
      width = c2num (undefined :: SIwidth NodeID v) :: Integer

      mkProbe = mkNL (\is -> (NodeAttr {nLabel = "probe: " ++ str, nShape = Sbox}, map inp is))
                  >>> arr (fst . runStateM structure . genericReplicate width)

instance ArrowInit (NLArrow detail) where
  isInitialState = mkNL (const (NodeAttr {nLabel = "isInitialState", nShape = Sbox}, []))

----------------------------------------

mkNonDet :: forall detail v. Structure NodeID v
         => Bool
         -> NLArrow detail (v, v) v
mkNonDet fair = proc (v0, v1) ->
    mkND -< zip (destructure v0) (destructure v1)
  where
    width = c2num (undefined :: SIwidth NodeID v) :: Integer

    l = if fair then "fair nondet" else "nondet"
    mkMux1 = mkNL (\(x, y) ->
                       ( NodeAttr {nLabel = "", nShape = Sparallelogram},
                         [ inp x, inp y]))
    mkND
     | width == 1 =
         mkNL (\ [(x, y)] ->
                    (NodeAttr {nLabel = l, nShape = Sparallelogram}, [ inp x, inp y ]))
          >>> arr (fst . runStateM structure . (:[]))
     | otherwise =
         note l $ proc asbs ->
           do zs <- (| (mapAC width) (\ab -> mkMux1 -< ab) |) asbs
              returnA -< fst (runStateM structure zs)

instance Structure NodeID v => ArrowNonDet (NLArrow detail) v where
  nondetA = mkNonDet false
  nondetFairA = mkNonDet true

instance Structure NodeID v => ArrowUnsafeNonDet (NLArrow detail) v where
  unsafeNonDetAC predA newA = note "unsafeNonDetAC" $ proc env ->
    do v <- vInit -< ()
       p <- predA -< (env, v)
       n  <- newA -< env
       mkNDI -< (p, n)
    where
      width = c2num (undefined :: SIwidth NodeID v) :: Integer

      vInit = mkNL (\_ -> (NodeAttr {nLabel = "nondet v", nShape = Sbox}, []))
                  >>> arr (fst . runStateM structure . genericReplicate width)

      mkNDI = mkNL (\(p, n) ->
                       ( NodeAttr {nLabel = "", nShape = Sparallelogram},
                         [ inpn "pred" p, inpn "new" n] ))
                  >>> arr (fst . runStateM structure . genericReplicate width)

----------------------------------------

instance Structure NodeID obs => ArrowAgent (NLArrow detail) obs where
  agent aid f = note ("Agent: " ++ aid) $
      f <<< arr (fst . runStateM structure) <<< mkObs <<< arr destructure
    where
      width = c2num (undefined :: SIwidth NodeID obs) :: Integer

      mkObs
        | width == 1 =
            mkNL (\[v] ->
                    ( NodeAttr {nLabel = "obs for " ++ aid, nShape = Sbox},
                      [ inp v ] ))
               >>> arr (:[])
        | otherwise = note ("obs for " ++ aid) $
            mapA width (mkNL (\v ->
                    ( NodeAttr {nLabel = "", nShape = Sbox},
                      [ inp v ] )))

{-
FIXME
instance (Arrow (~>), StructureDest Wire iobs, StructureDest Wire cobs)
      => ArrowBroadcast (NLArrow detail) iobs cobs where
  -- broadcast :: Card size
  --           => SizedList size (AgentID, (iobs, cobs) ~> c)
  --           -> (env ~> SizedList size iobs) -- ^ The initial observations
  --           -> (env ~> cobs) -- ^ The recurring common observation
  --           -> (env ~> SizedList size c)
  broadcast agents iarr carr = note "Broadcast" $ proc env ->
    do iobs <- iarr -< env
       cobs <- carr -< env
       let obs = zipWithSL id (iobs, replicateSL cobs)
       zipWithSLs (uncurry agent) agents -< obs
-}

instance ArrowKTest (NLArrow detail) where
  kTest f = mkNLconst (NodeAttr {nLabel = "kbpTest: " ++ show f, nShape = Sbox})

-------------------------------------------------------------------
-- NetList top-level.
-------------------------------------------------------------------

-- | Generate a "NetList" from a circuit. The @detail@ parameter needs
-- to be instantiated.
runNL_prim :: forall b c detail. (Structure NodeID b, StructureDest NodeID c)
           => NLArrow detail b c -> NetList
runNL_prim nlArr =
  let nodeIDs = map NodeID [ 0 .. ]
      numInputs = c2num (undefined :: SIwidth NodeID b) :: Integer
      (inVal, _) = runStateM structure nodeIDs
      inputLabels = genericTake numInputs nodeIDs
      ((nl, c), s') = runStateM (runNLArrow nlArr inVal) (genericDrop numInputs nodeIDs)
      (ns, al) = nl
      inputNodes = mkInputNodes inputLabels
      outputNodes = mkOutputNodes (Prelude.zip s' (destructure c))
   in outputNodes
        `nlAppend`
          (inputNodes `catNodes` ns, al)
  where
     mkInputNode i = Node {nID = i, nAttrs = NodeAttr {nLabel = "in_" ++ show i, nShape = Stext}}

     mkInputNodes = SubNetList "Inputs" . foldr f NoNodes
       where f i ns = mkInputNode i `catNodes` ns

     mkOutputNode i = Node {nID = i, nAttrs = NodeAttr {nLabel = "out_" ++ show i, nShape = Stext}}

     mkOutputNodes :: [(NodeID, NodeID)] -> NetList
     mkOutputNodes = first (SubNetList "Outputs") . foldr f nlEmpty
       where f (i, w) (ns, al) = ( mkOutputNode i `catNodes` ns
                                 , (i, [outp w]) : al )

-- | Generate an architecture-level "NetList" from a circuit.
runNL :: (Structure NodeID b, StructureDest NodeID c)
      => NLArrow ArchView b c -> NetList
runNL = runNL_prim

-- | Generate a bit-level "NetList" from a circuit.
runNLbits :: (Structure NodeID b, StructureDest NodeID c)
          => NLArrow BitView b c -> NetList
runNLbits = runNL_prim

-------------------------------------------------------------------
-- Conversion functions.
-------------------------------------------------------------------

-- | Convert a 'NetList' into dot (graphviz) format.
-- FIXME need to uniquify all cluster names (level is not enough)
nl2dot :: NetList -> String
nl2dot (nodes, assoclist) = unlines $
    [ "digraph Circ {"
    , "\trankdir=LR;"
    , rNodes
    , rEdges
    ]
  where
    rNodes = fst (runStateM (mkNodes (1 :: Int) nodes) (1 :: Int)) ""

    mkNodes l n =
      case n of
        NoNodes -> return id
        Node {} -> return $ showString $
                     replicate l '\t' ++ "node " ++ mkNodeAttrs (nAttrs n)
                                      ++ " " ++ show (nID n) ++ ";\n"
        Nodes n1 n2 -> liftM2 (.) (mkNodes l n1) (mkNodes l n2)
        SubNetList _name NoNodes -> return id
        SubNetList name ns ->
          do i <- nextUniqueSM
             snl <- mkNodes (succ l) ns
             return $ mkSubNetList l name i snl

    mkNodeAttrs attrs = "[label=\"" ++ nLabel attrs ++ "\", shape=" ++ show (nShape attrs) ++ "]"

    mkSubNetList l name i snl =
          showString (replicate l '\t' ++ "subgraph cluster_subcirc_" ++ show i ++ " {\n"
                   ++ replicate (succ l) '\t' ++ "label=\"" ++ name ++ "\";\n")
        . rank
        . snl
        . showString (replicate l '\t' ++ "}\n")
      where
        rank | name == "Inputs" = showString (replicate (succ l) '\t' ++ "rank=source;\n")
             | name == "Outputs" = showString (replicate (succ l) '\t' ++ "rank=sink;\n")
             | otherwise = id

    rEdges = foldr mkEdges id assoclist $ "}"

    mkEdges (n, inputs) str = foldr (mkEdge n) str inputs
    mkEdge n (Wire input attrs) str =
        str . showChar '\t'
      . shows input . showString " -> " . shows n
      . mkEdgeAttrs attrs
      . showString ";\n"

    mkEdgeAttrs wA =
      case wA of
        NoWireAttrs -> id
        WireAttr l -> showString ("[label=\"" ++ l ++ "\"]")

-- FIXME perhaps generalise the underlying arrow, or hard wire NLArrow detail to (->).
dotNL :: (Structure NodeID b, StructureDest NodeID c)
      => FilePath -> NLArrow ArchView b c -> IO ()
dotNL f = writeFile f . nl2dot . runNL

-- FIXME perhaps generalise the underlying arrow, or hard wire NLArrow detail to (->).
dotNLbits :: (Structure NodeID b, StructureDest NodeID c)
          => FilePath -> NLArrow BitView b c -> IO ()
dotNLbits f = writeFile f . nl2dot . runNLbits
