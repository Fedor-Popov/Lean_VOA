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

theorem cycChk115 : zeroL (wordS e7T 133 [110, 76] [(132, 1)] ++ scale (-(-1)) [(115, 1)]) = true := by
  decide +kernel

theorem cycChk116 : zeroL (wordS e7T 133 [114] [(132, 1)] ++ scale (-(-1)) [(116, 1)]) = true := by
  decide +kernel

theorem cycChk117 : zeroL (wordS e7T 133 [113] [(132, 1)] ++ scale (-(-1)) [(117, 1)]) = true := by
  decide +kernel

theorem cycChk118 : zeroL (wordS e7T 133 [112] [(132, 1)] ++ scale (-(-1)) [(118, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk115
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk116
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk117
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk118
