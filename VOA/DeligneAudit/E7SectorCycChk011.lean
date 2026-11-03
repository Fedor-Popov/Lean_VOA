/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorIntegerTable
import VOA.DeligneAudit.E6SectorDefs

/-!
# `E₇` coadjoint cyclicity: Boolean word checks (depth 2 from `δ_{132}`, light imports)
-/

namespace VOA.DeligneAudit.DeligneCarrier.E7

open VOA.AffineGeneral.SCLie VOA.DeligneAudit.E6SectorSparse

set_option linter.style.longLine false

theorem cycChk11 : zeroL (wordS e7T 133 [131, 82] [(132, 1)] ++ scale (-(-1)) [(11, 1)]) = true := by
  decide +kernel

theorem cycChk12 : zeroL (wordS e7T 133 [129, 94] [(132, 1)] ++ scale (-(1)) [(12, 1)]) = true := by
  decide +kernel

theorem cycChk13 : zeroL (wordS e7T 133 [132, 76] [(132, 1)] ++ scale (-(-1)) [(13, 1)]) = true := by
  decide +kernel

theorem cycChk14 : zeroL (wordS e7T 133 [128, 103] [(132, 1)] ++ scale (-(1)) [(14, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk11
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk12
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk13
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk14
