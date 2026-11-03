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

theorem cycChk83 : zeroL (wordS e7T 133 [124, 88] [(132, 1)] ++ scale (-(-1)) [(83, 1)]) = true := by
  decide +kernel

theorem cycChk84 : zeroL (wordS e7T 133 [126, 82] [(132, 1)] ++ scale (-(1)) [(84, 1)]) = true := by
  decide +kernel

theorem cycChk85 : zeroL (wordS e7T 133 [128, 76] [(132, 1)] ++ scale (-(1)) [(85, 1)]) = true := by
  decide +kernel

theorem cycChk86 : zeroL (wordS e7T 133 [125, 82] [(132, 1)] ++ scale (-(-1)) [(86, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk83
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk84
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk85
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk86
