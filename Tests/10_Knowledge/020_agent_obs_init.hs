-- Check that the agent's observation is intuitively correct.

module T where

import Tests.KBPBasis

kbpt = kTest ("kbp" `knows_hat` "bit")
kbp = agent "kbp" kbpt

c = proc () ->
      do rec bit <- (| delayAC (nondetBitA -< ()) (notA -< bit) |)
         probeA "bit" -< bit
         probeA "out" <<< kbp -< ()

m = isConstructive c

-- Synthesis using the clock semantics
Just (_kautos_clk, mclk, _) = clockSynth MinNone c
ctlM_clk = mkCTLModel mclk

-- Synthesis using the SPR semantics
Just (_kautos_spr, mspr, _) = singleSPRSynth MinNone c
ctlM_spr = mkCTLModel mspr

test_clock_bit_alternates = isOK (mc ctlM_clk (ag (probe "bit" <-> ax (neg (probe "bit")))))
test_spr_bit_alternates = isOK (mc ctlM_spr (ag (probe "bit" <-> ax (neg (probe "bit")))))

-- The bit is unobservable, so the agent never knows anything about it.
test_clock_never_knows = isOK (mc ctlM_clk (ag (neg (probe "out"))))
test_spr_never_knows = isOK (mc ctlM_spr (ag (neg (probe "out"))))
