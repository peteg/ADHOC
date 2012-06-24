-- Check that the register works.

module T where

import Data.Maybe hiding ( Maybe(..), maybe )

import Test.QuickCheck hiding ( conjoin, disjoin )

import ADHOC
import ADHOC.Control.Kesterel
import ADHOC.NonDet
import ADHOC.ModelChecker.CTL

import Broadcast

pid = "probe"

--------------------

e0 = registerPE pid $ \(reg_set, reg_reset, reg_val) ->
  (loopE $ emitE reg_set >>> pauseE)

Just (m0, _) = isConstructive (runE e0)
ctlM0 = mkCTLModel m0

test_set = isOK (mc ctlM0 (ag (probe pid)))

--------------------

e1 = registerPE pid $ \(reg_set, reg_reset, reg_val) ->
  (loopE $ emitE reg_set >>> pauseE >>> emitE reg_reset >>> pauseE)

Just (m1, _) = isConstructive (runE e1)
ctlM1 = mkCTLModel m1

test_reset_fail = isFailure (mc ctlM1 (ag (probe pid)))
test_reset_ok = isOK (mc ctlM1 (ag (probe pid <-> ax (neg (probe pid)))))
test_reset_ok_init = isOK (mc ctlM1 (probe pid))

--------------------

e2 = registerPE pid $ \(reg_set, reg_reset, reg_val) ->
  (emitE reg_set >>> loopE pauseE)

Just (m2, _) = isConstructive (runE e2)
ctlM2 = mkCTLModel m2

test_set_once = isOK (mc ctlM2 (ag (probe pid)))

--------------------

e3 = registerPE pid $ \(reg_set, reg_reset, reg_val) ->
  loopE pauseE

Just (m3, _) = isConstructive (runE e3)
ctlM3 = mkCTLModel m3

test_set_never = isOK (mc ctlM3 (ag (neg (probe pid))))

--------------------

pid2 = "another probe"

e4 = registerPE pid $ \(reg_set, reg_reset, reg_val) -> (
    ( loopE $ pauseE >>> emitE reg_reset >>> pauseE >>> emitE reg_set)
  ||||
    ( signalE $ \s -> probeSigE pid2 s >>> loopE (unlessE reg_val (emitE s) >>> pauseE) ) )

Just (m4, _) = isConstructive (runE e4)
ctlM4 = mkCTLModel m4

test_par_always_init = isOK (mc ctlM4 (neg (probe pid) /\ probe pid2))
test_par_always = isOK (mc ctlM4 (ag (probe pid <-> neg (probe pid2))))

--------------------

e5 = registerPE pid $ \(reg_set, reg_reset, reg_val) ->
  (loopE $ emitE reg_set >>> emitE reg_reset >>> pauseE)

Just (m5, _) = isConstructive (runE e5)
ctlM5 = mkCTLModel m5

test_set_reset = isOK (mc ctlM5 (ag (neg (probe pid))))
