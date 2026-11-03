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

theorem cycChk67 : zeroL (wordS e7T 133 [132, 130] [(132, 1)] ++ scale (-(1)) [(67, 1)]) = true := by
  decide +kernel

theorem cycChk68 : zeroL (wordS e7T 133 [132, 131] [(132, 1)] ++ scale (-(1)) [(68, 1)]) = true := by
  decide +kernel

theorem cycChk69 : zeroL (wordS e7T 133 [132, 132] [(132, 1)] ++ scale (-(2)) [(69, 1)]) = true := by
  decide +kernel

theorem cycChk70 : zeroL (wordS e7T 133 [124, 99] [(132, 1)] ++ scale (-(1)) [(70, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk67
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk68
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk69
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk70
