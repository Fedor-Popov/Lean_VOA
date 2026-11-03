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

theorem cycChk27 : zeroL (wordS e7T 133 [131, 99] [(132, 1)] ++ scale (-(-1)) [(27, 1)]) = true := by
  decide +kernel

theorem cycChk28 : zeroL (wordS e7T 133 [130, 104] [(132, 1)] ++ scale (-(1)) [(28, 1)]) = true := by
  decide +kernel

theorem cycChk29 : zeroL (wordS e7T 133 [131, 100] [(132, 1)] ++ scale (-(-1)) [(29, 1)]) = true := by
  decide +kernel

theorem cycChk30 : zeroL (wordS e7T 133 [132, 93] [(132, 1)] ++ scale (-(1)) [(30, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk27
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk28
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk29
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk30
