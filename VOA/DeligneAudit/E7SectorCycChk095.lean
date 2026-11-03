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

theorem cycChk95 : zeroL (wordS e7T 133 [124, 76] [(132, 1)] ++ scale (-(1)) [(95, 1)]) = true := by
  decide +kernel

theorem cycChk96 : zeroL (wordS e7T 133 [121, 82] [(132, 1)] ++ scale (-(-1)) [(96, 1)]) = true := by
  decide +kernel

theorem cycChk97 : zeroL (wordS e7T 133 [123, 76] [(132, 1)] ++ scale (-(-1)) [(97, 1)]) = true := by
  decide +kernel

theorem cycChk98 : zeroL (wordS e7T 133 [122, 76] [(132, 1)] ++ scale (-(-1)) [(98, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk95
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk96
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk97
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk98
