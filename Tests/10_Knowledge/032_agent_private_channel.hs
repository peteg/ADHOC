-- Like 031 but two agents communicate privately in a broadcast
-- setting with a third oblivious.

-- Probably what Rivest had in mind with his "oblivious transfer".

-- It makes sense to use common knowledge here: the third party knows
-- the bit is common knowledge to "1" and "2" but doesn't know the bit
-- herself.

module T where

import Prelude hiding ( id )
import Tests.KBPBasis

-- "1" always knows "bit", and knows "2" knows that "1" knows the bit.
-- "2" always knows "bit", and knows "1" knows that "2" knows the bit.
-- "3" knows that "1" and "2" know, but does not know herself.
kbp1 = agent "1" ((kTest $ "1" `knows_hat` "datum")
              &&& (kTest $ "1" `knows_hat` ("2" `knows_hat` ("1" `knows_hat` "datum"))))

kbp2 = agent "2" ((kTest $ "2" `knows_hat` "datum")
              &&& (kTest $ "2" `knows_hat` ("1" `knows_hat` ("2" `knows_hat` "datum"))))

kbp3 = agent "3" ((kTest $ "3" `knows_hat` ("1" `knows_hat` "datum" /\ "2" `knows_hat` "datum"))
              &&& (kTest $ neg ("3" `knows_hat` "datum")))

-- Initially "1" and "2" can see the "key", and "3" cannot.
agent_arrs = mkSizedListA
    [ ("1", id,    probeA "out1" *** probeA "out2" <<< kbp1)
    , ("2", id,    probeA "out3" *** probeA "out4" <<< kbp2)
    , ("3", zeroA, probeA "out5" *** probeA "out6" <<< kbp3) ]
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
test_spr_kbps_ok3 = isOK (mc ctlM_spr (ag (probe "out3")))
test_spr_kbps_ok4 = isOK (mc ctlM_spr (ag (probe "out4")))
test_spr_kbps_ok5 = isOK (mc ctlM_spr (ag (probe "out5")))
test_spr_kbps_ok6 = isOK (mc ctlM_spr (ag (probe "out6")))
