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

theorem cycChk127 : zeroL (wordS e7T 133 [94] [(132, 1)] ++ scale (-(-1)) [(127, 1)]) = true := by
  decide +kernel

theorem cycChk128 : zeroL (wordS e7T 133 [93] [(132, 1)] ++ scale (-(1)) [(128, 1)]) = true := by
  decide +kernel

theorem cycChk129 : zeroL (wordS e7T 133 [88] [(132, 1)] ++ scale (-(-1)) [(129, 1)]) = true := by
  decide +kernel

theorem cycChk130 : zeroL (wordS e7T 133 [82] [(132, 1)] ++ scale (-(1)) [(130, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk127
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk128
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk129
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk130
