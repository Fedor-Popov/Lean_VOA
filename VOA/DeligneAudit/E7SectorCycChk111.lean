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

theorem cycChk111 : zeroL (wordS e7T 133 [114, 76] [(132, 1)] ++ scale (-(1)) [(111, 1)]) = true := by
  decide +kernel

theorem cycChk112 : zeroL (wordS e7T 133 [118] [(132, 1)] ++ scale (-(1)) [(112, 1)]) = true := by
  decide +kernel

theorem cycChk113 : zeroL (wordS e7T 133 [117] [(132, 1)] ++ scale (-(1)) [(113, 1)]) = true := by
  decide +kernel

theorem cycChk114 : zeroL (wordS e7T 133 [116] [(132, 1)] ++ scale (-(1)) [(114, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk111
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk112
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk113
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk114
