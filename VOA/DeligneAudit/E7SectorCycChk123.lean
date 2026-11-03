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

theorem cycChk123 : zeroL (wordS e7T 133 [104] [(132, 1)] ++ scale (-(-1)) [(123, 1)]) = true := by
  decide +kernel

theorem cycChk124 : zeroL (wordS e7T 133 [103] [(132, 1)] ++ scale (-(1)) [(124, 1)]) = true := by
  decide +kernel

theorem cycChk125 : zeroL (wordS e7T 133 [100] [(132, 1)] ++ scale (-(1)) [(125, 1)]) = true := by
  decide +kernel

theorem cycChk126 : zeroL (wordS e7T 133 [99] [(132, 1)] ++ scale (-(-1)) [(126, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk123
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk124
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk125
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk126
