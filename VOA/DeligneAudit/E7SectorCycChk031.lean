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

theorem cycChk31 : zeroL (wordS e7T 133 [132, 94] [(132, 1)] ++ scale (-(1)) [(31, 1)]) = true := by
  decide +kernel

theorem cycChk32 : zeroL (wordS e7T 133 [131, 103] [(132, 1)] ++ scale (-(-1)) [(32, 1)]) = true := by
  decide +kernel

theorem cycChk33 : zeroL (wordS e7T 133 [130, 108] [(132, 1)] ++ scale (-(1)) [(33, 1)]) = true := by
  decide +kernel

theorem cycChk34 : zeroL (wordS e7T 133 [131, 104] [(132, 1)] ++ scale (-(-1)) [(34, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk31
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk32
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk33
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk34
