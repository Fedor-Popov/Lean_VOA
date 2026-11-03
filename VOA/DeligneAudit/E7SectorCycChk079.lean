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

theorem cycChk79 : zeroL (wordS e7T 133 [128, 82] [(132, 1)] ++ scale (-(-1)) [(79, 1)]) = true := by
  decide +kernel

theorem cycChk80 : zeroL (wordS e7T 133 [129, 76] [(132, 1)] ++ scale (-(-1)) [(80, 1)]) = true := by
  decide +kernel

theorem cycChk81 : zeroL (wordS e7T 133 [127, 82] [(132, 1)] ++ scale (-(1)) [(81, 1)]) = true := by
  decide +kernel

theorem cycChk82 : zeroL (wordS e7T 133 [130] [(132, 1)] ++ scale (-(-1)) [(82, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk79
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk80
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk81
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk82
