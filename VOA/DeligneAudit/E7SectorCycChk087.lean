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

theorem cycChk87 : zeroL (wordS e7T 133 [127, 76] [(132, 1)] ++ scale (-(-1)) [(87, 1)]) = true := by
  decide +kernel

theorem cycChk88 : zeroL (wordS e7T 133 [129] [(132, 1)] ++ scale (-(1)) [(88, 1)]) = true := by
  decide +kernel

theorem cycChk89 : zeroL (wordS e7T 133 [124, 82] [(132, 1)] ++ scale (-(-1)) [(89, 1)]) = true := by
  decide +kernel

theorem cycChk90 : zeroL (wordS e7T 133 [126, 76] [(132, 1)] ++ scale (-(-1)) [(90, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk87
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk88
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk89
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk90
