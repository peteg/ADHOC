-- Verify the parallel operation handles exit codes properly.
module T where

import Tests.KesterelBasis

{-
FIXME
Check |||| wrt exceptions. Write more tests:
- exns
- termination
- pause
-}

e1 = signalE $ \(s0, s1, s2) -> probeSigE "s0" s0 >>> probeSigE "s1" s1 >>> probeSigE "s2" s2 >>>
  (emitE s0 |||| emitE s1) >>> emitE s2
c1 = unitA >>> runE e1 >>> probeA "term"

Just (m1, (_, ())) = isConstructive c1
ctlM1 = mkCTLModel m1

test_c1 = isOK (mc ctlM1 (probe "s0" /\ probe "s1" /\ probe "s2" /\ probe "term"))

--------------------

e2 = signalE $ \(s0, s1, s2) -> probeSigE "s0" s0 >>> probeSigE "s1" s1 >>> probeSigE "s2" s2 >>>
  (emitE s0 |||| (emitE s1 >>> pauseE)) >>> emitE s2
c2 = unitA >>> runE e2 >>> probeA "term"

Just (m2, (_, ())) = isConstructive c2
ctlM2 = mkCTLModel m2

test_c2 = isOK (mc ctlM2 (probe "s0" /\ probe "s1" /\ neg (probe "s2") /\ neg (probe "term")))
test_c2_s2 = isOK (mc ctlM2 (neg (probe "s2") /\ ax (probe "s2")))
test_c2_term = isOK (mc ctlM2 (neg (probe "term") /\ ax (probe "term")))

--------------------

e3 = signalE $ \(s0, s1, s2) -> probeSigE "s0" s0 >>> probeSigE "s1" s1 >>> probeSigE "s2" s2 >>>
  (catchE $ \exn1 -> emitE s0 |||| (throwE exn1 >>> emitE s1)) >>> emitE s2
c3 = unitA >>> runE e3 >>> probeA "term"

Just (m3, (_, ())) = isConstructive c3
ctlM3 = mkCTLModel m3

test_c3 = isOK (mc ctlM3 (probe "s0" /\ neg (probe "s1") /\ probe "s2" /\ probe "term"))

--------------------

e4 = signalE $ \(s0, s1, s2) -> probeSigE "s0" s0 >>> probeSigE "s1" s1 >>> probeSigE "s2" s2 >>>
  (catchE $ \exn1 -> (emitE s0 >>> pauseE) |||| (emitE s1 >>> throwE exn1)) >>> emitE s2
c4 = unitA >>> runE e4 >>> probeA "term"

Just (m4, (_, ())) = isConstructive c4
ctlM4 = mkCTLModel m4

test_c4 = isOK (mc ctlM4 (probe "s0" /\ probe "s1" /\ probe "s2" /\ probe "term" /\ ax (ag (neg (probe "term")))))

--------------------

e5 = signalE $ \(s0, s1, s2) -> probeSigE "s0" s0 >>> probeSigE "s1" s1 >>> probeSigE "s2" s2 >>>
  (catchE $ \exn1 -> (pauseE >>> emitE s0 >>> throwE exn1)
                |||| (emitE s1 >>> throwE exn1))
  >>> emitE s2
c5 = unitA >>> runE e5 >>> probeA "term"

Just (m5, (_, ())) = isConstructive c5
ctlM5 = mkCTLModel m5

test_c5 = isOK (mc ctlM5 (ag (neg (probe "s0")) /\ probe "s1" /\ probe "s2" /\ probe "term" /\ ax (ag (neg (probe "term")))))

--------------------
