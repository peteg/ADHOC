-- Check that the agent's observation is intuitively correct.

module T where

import Tests.KBPBasis

kbp = agent "kbp" $ kTest ("kbp" `knows_hat` "bit")

c = proc () ->
  do boot <- delayAC trueA falseA -< ()
     bit <- nondetBitA -< ()
     obs <- andA -< (boot, bit)
     probeA "bit" -< bit
     probeA "out" <<< kbp -< obs

-- Synthesis using the clock semantics
Just (_kautos_clk, mclk, _) = clockSynth MinNone c
ctlM_clk = mkCTLModel mclk

-- Synthesis using the SPR semantics
Just (_kautos_spr, mspr, _) = singleSPRSynth MinNone c
ctlM_spr = mkCTLModel mspr

-- In branching time, the bit could always go either way.
test_clock_bit_alternates = isOK (mc ctlM_clk (ag (ex (probe "bit") /\ ex (neg (probe "bit")))))
test_spr_bit_alternates = isOK (mc ctlM_spr (ag (ex (probe "bit") /\ ex (neg (probe "bit")))))

-- Initially the agent knows the bit.
test_clock_knows_init = isOK (mc ctlM_clk (probe "out"))
test_spr_knows_init = isOK (mc ctlM_spr (probe "out"))

-- Later it doesn't.
test_clock_oblivious_later = isOK (mc ctlM_clk (ax (ag (neg (probe "out")))))
test_spr_oblivious_later = isOK (mc ctlM_spr (ax (ag (neg (probe "out")))))
