-- Like 032: two agents communicate privately in a broadcast setting
-- with a third oblivious, but use common knowledge as the correctness
-- property.

-- Probably what Rivest had in mind with his "oblivious transfer".

module T where

import Prelude hiding ( id )
import Tests.KBPBasis

-- It is common knowledge to everyone that "1" and "2" always know
-- "bit", and "3" does not know the bit. We only need to look at it
-- from "1"'s point of view, but add in the others for some
-- cross-checking.
kbp1 = agent "1" $ kTest $ ["1", "2", "3"] `cknows_hat` (["1", "2"] `cknows_hat` "datum"
                                                        /\ neg ("3" `knows_hat` "datum"))
kbp2 = agent "2" $ kTest $ ["1", "2"] `cknows_hat` "datum"
kbp3 = agent "3" $ kTest $ ["3"] `cknows_hat` "datum"

-- Initially "1" and "2" can see the "key", and "3" cannot.
agent_arrs = mkSizedListA
    [ ("1", id,    probeA "out1" <<< kbp1)
    , ("2", id,    probeA "out2" <<< kbp2)
    , ("3", zeroA, probeA "out3" <<< kbp3) ]
     `withLength` (undefined :: Three)

c = proc () ->
  do -- Flip a bit and latch it.
     key <- nondetLatchAC trueA -< ()
     -- Flip a bit at each time step.
     datum <- nondetBitA -< ()
     bit <- xorA -< (key, datum)

     probeA "key" -< key
     probeA "datum" -< datum
     probeA "bit" -< bit

     (| (broadcast agent_arrs)
           (returnA -< key)
           (returnA -< bit) |)

-- Synthesis using the broadcast SPR semantics.
Just (_kautos_spr, mspr, _) = broadcastSprSynth MinNone c
ctlM_spr = mkCTLModel mspr

-- The key never changes.
test_spr_key_stable = isOK (mc ctlM_spr (probe "key" <-> ag (probe "key")))

-- The bit could always go either way.
test_spr_bit_alternates = isOK (mc ctlM_spr (ag (ex (probe "bit") /\ ex (neg (probe "bit")))))

-- The KBPs play out.
test_spr_kbps_ok1 = isOK (mc ctlM_spr (ag (probe "out1")))
test_spr_kbps_ok2 = isOK (mc ctlM_spr (ag (probe "out2")))
test_spr_kbps_ok3 = isOK (mc ctlM_spr (ag (neg (probe "out3"))))
