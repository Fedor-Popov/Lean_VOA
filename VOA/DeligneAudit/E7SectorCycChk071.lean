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

theorem cycChk71 : zeroL (wordS e7T 133 [126, 93] [(132, 1)] ++ scale (-(-1)) [(71, 1)]) = true := by
  decide +kernel

theorem cycChk72 : zeroL (wordS e7T 133 [128, 88] [(132, 1)] ++ scale (-(1)) [(72, 1)]) = true := by
  decide +kernel

theorem cycChk73 : zeroL (wordS e7T 133 [129, 82] [(132, 1)] ++ scale (-(-1)) [(73, 1)]) = true := by
  decide +kernel

theorem cycChk74 : zeroL (wordS e7T 133 [130, 76] [(132, 1)] ++ scale (-(-1)) [(74, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk71
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk72
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk73
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk74
