-- Nested knowledge, like 020_agent_obs_init

-- This is a way for the environment to communicate privately with one
-- of the agents in a broadcast setting.

-- Probably what Rivest had in mind with his "oblivious transfer".

module T where

import Prelude hiding ( id )
import Tests.KBPBasis

-- "1" always knows "bit", and knows "2" knows that "1" knows the bit.
-- "2" knows that "1" knows, but does not know herself.
kbp1 = agent "1" ((kTest $ "1" `knows_hat` "datum")
              &&& (kTest $ "1" `knows_hat` ("2" `knows_hat` ("1" `knows_hat` "datum"))))

kbp2 = agent "2" ((kTest $ "2" `knows_hat` ("1" `knows_hat` "datum"))
              &&& (kTest $ neg ("2" `knows_hat` "datum")))

-- Initially "1" can see the "key", and "2" cannot.
agent_arrs = mkSizedListA
    [ ("1", id,    probeA "out1" *** probeA "out4" <<< kbp1)
    , ("2", zeroA, probeA "out2" *** probeA "out3" <<< kbp2) ]

c = proc () ->
  do -- Flip a bit and latch it.
     key <- (| nondetLatchAC (trueA -< ()) |)
     -- Flip a bit at each time step.
     datum <- nondetBitA -< ()
     bit <- xorA -< (key, datum)

     probeA "key" -< key
     probeA "datum" -< datum
     probeA "bit" -< bit

     (| (broadcast (agent_arrs `withLength` (undefined :: Two)))
           (returnA -< key)
           (returnA -< bit) |)

-- Synthesis using the clock semantics
Just (_kautos_clk, mclk, _) = clockSynth MinNone c
ctlM_clk = mkCTLModel mclk

-- Synthesis using the broadcast SPR semantics.
Just (_kautos_spr, mspr, _) = broadcastSprSynth MinNone c
ctlM_spr = mkCTLModel mspr

-- The key never changes.
test_clk_key_stable = isOK (mc ctlM_clk (probe "key" <-> ag (probe "key")))
test_spr_key_stable = isOK (mc ctlM_spr (probe "key" <-> ag (probe "key")))

-- The bit could always go either way.
test_clk_bit_alternates = isOK (mc ctlM_clk (ag (ex (probe "bit") /\ ex (neg (probe "bit")))))
test_spr_bit_alternates = isOK (mc ctlM_spr (ag (ex (probe "bit") /\ ex (neg (probe "bit")))))

-- The KBPs play out.
-- The first shows that the clock semantics is too weak to play this game.
-- Then again, we don't need to use broadcast there either.
test_clk_kbps_ok1 = not (isOK (mc ctlM_clk (ag (probe "out1"))))
test_clk_kbps_ok2 = isOK (mc ctlM_clk (ag (probe "out2")))
test_clk_kbps_ok3 = isOK (mc ctlM_clk (ag (probe "out3")))
test_clk_kbps_ok4 = isOK (mc ctlM_clk (ag (probe "out4")))

test_spr_kbps_ok1 = isOK (mc ctlM_spr (ag (probe "out1")))
test_spr_kbps_ok2 = isOK (mc ctlM_spr (ag (probe "out2")))
test_spr_kbps_ok3 = isOK (mc ctlM_spr (ag (probe "out3")))
test_spr_kbps_ok4 = isOK (mc ctlM_spr (ag (probe "out4")))
