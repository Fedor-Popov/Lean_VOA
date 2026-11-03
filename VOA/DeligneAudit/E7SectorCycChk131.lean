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

theorem cycChk131 : zeroL (wordS e7T 133 [76] [(132, 1)] ++ scale (-(1)) [(131, 1)]) = true := by
  decide +kernel

theorem cycChk132 : zeroL (wordS e7T 133 [0] [(132, 1)] ++ scale (-(1)) [(132, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk131
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk132
