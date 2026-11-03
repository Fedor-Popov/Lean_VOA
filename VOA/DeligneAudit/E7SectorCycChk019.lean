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

theorem cycChk19 : zeroL (wordS e7T 133 [132, 82] [(132, 1)] ++ scale (-(1)) [(19, 1)]) = true := by
  decide +kernel

theorem cycChk20 : zeroL (wordS e7T 133 [129, 103] [(132, 1)] ++ scale (-(-1)) [(20, 1)]) = true := by
  decide +kernel

theorem cycChk21 : zeroL (wordS e7T 133 [130, 99] [(132, 1)] ++ scale (-(1)) [(21, 1)]) = true := by
  decide +kernel

theorem cycChk22 : zeroL (wordS e7T 133 [131, 93] [(132, 1)] ++ scale (-(-1)) [(22, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk19
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk20
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk21
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk22
