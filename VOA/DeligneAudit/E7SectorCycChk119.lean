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

theorem cycChk119 : zeroL (wordS e7T 133 [110] [(132, 1)] ++ scale (-(1)) [(119, 1)]) = true := by
  decide +kernel

theorem cycChk120 : zeroL (wordS e7T 133 [109] [(132, 1)] ++ scale (-(1)) [(120, 1)]) = true := by
  decide +kernel

theorem cycChk121 : zeroL (wordS e7T 133 [108] [(132, 1)] ++ scale (-(1)) [(121, 1)]) = true := by
  decide +kernel

theorem cycChk122 : zeroL (wordS e7T 133 [105] [(132, 1)] ++ scale (-(-1)) [(122, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk119
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk120
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk121
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk122
