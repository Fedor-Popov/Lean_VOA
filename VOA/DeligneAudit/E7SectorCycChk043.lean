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

theorem cycChk43 : zeroL (wordS e7T 133 [131, 112] [(132, 1)] ++ scale (-(-1)) [(43, 1)]) = true := by
  decide +kernel

theorem cycChk44 : zeroL (wordS e7T 133 [131, 113] [(132, 1)] ++ scale (-(-1)) [(44, 1)]) = true := by
  decide +kernel

theorem cycChk45 : zeroL (wordS e7T 133 [132, 108] [(132, 1)] ++ scale (-(1)) [(45, 1)]) = true := by
  decide +kernel

theorem cycChk46 : zeroL (wordS e7T 133 [132, 109] [(132, 1)] ++ scale (-(1)) [(46, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk43
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk44
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk45
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk46
