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

theorem cycChk103 : zeroL (wordS e7T 133 [124] [(132, 1)] ++ scale (-(-1)) [(103, 1)]) = true := by
  decide +kernel

theorem cycChk104 : zeroL (wordS e7T 133 [123] [(132, 1)] ++ scale (-(1)) [(104, 1)]) = true := by
  decide +kernel

theorem cycChk105 : zeroL (wordS e7T 133 [122] [(132, 1)] ++ scale (-(1)) [(105, 1)]) = true := by
  decide +kernel

theorem cycChk106 : zeroL (wordS e7T 133 [118, 76] [(132, 1)] ++ scale (-(-1)) [(106, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk103
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk104
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk105
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk106
