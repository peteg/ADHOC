-- Nested knowledge, like 020_agent_obs_init

module T where

import Tests.KBPBasis

-- "1" always knows "bit". "2" knows that "1" knows, but does not know
-- herself.
kbp1 = agent "1" $ kTest $ "1" `knows_hat` "bit"
kbp2 = agent "2" $ kTest $
          ("2" `knows_hat` ("1" `knows_hat` "bit"))
       /\ neg ("2" `knows_hat` "bit")

c = proc () ->
  do bit1 <- nondetBitA -< ()
     bit2 <- nondetBitA -< ()
     bit <- xorA -< (bit1, bit2)
     probeA "bit" -< bit
     probeA "out1" <<< kbp1 -< (bit1, bit)
     probeA "out2" <<< kbp2 -< bit

-- Synthesis using the clock semantics
Just (_kautos_clk, mclk, _) = clockSynth MinNone c
ctlM_clk = mkCTLModel mclk

-- The bit could always go either way.
test_clock_bit_alternates = isOK (mc ctlM_clk (ag (ex (probe "bit") /\ ex (neg (probe "bit")))))

-- The KBPs play out.
test_clock_kbps_ok = isOK (mc ctlM_clk ((ag (probe "out1")) /\ ag (neg (probe "out2"))))
