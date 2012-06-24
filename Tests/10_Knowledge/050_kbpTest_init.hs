-- If we allow a kTest as an initialiser, we can easily get a
-- paradox.

module T where

import Prelude hiding ( id )
import Tests.KBPBasis

import ADHOC.Knowledge.Clock

-- Agent "1" knows a bit iff the bit is false.
c = proc () ->
  do rec x <- (| nondetLatchAC
                   (\x -> agent "1" (kTest $ "1" `knows` neg (probe "x")) <<< probeA "x" <<< idB -< x) |)
     returnA -< x

-- Synthesis using the clock semantics
Just (_kautos_clk, mclk, _) = clockSynth MinNone c
ctlM_clk = mkCTLModel mclk

-- What is the value of the bit?
test_clock_bit1 = isOK (mc ctlM_clk (probe "x"))
test_clock_bit0 = isOK (mc ctlM_clk (neg (probe "x")))
