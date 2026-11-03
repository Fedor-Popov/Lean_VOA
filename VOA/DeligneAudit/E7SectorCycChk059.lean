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

theorem cycChk59 : zeroL (wordS e7T 133 [132, 122] [(132, 1)] ++ scale (-(1)) [(59, 1)]) = true := by
  decide +kernel

theorem cycChk60 : zeroL (wordS e7T 133 [132, 123] [(132, 1)] ++ scale (-(1)) [(60, 1)]) = true := by
  decide +kernel

theorem cycChk61 : zeroL (wordS e7T 133 [132, 124] [(132, 1)] ++ scale (-(1)) [(61, 1)]) = true := by
  decide +kernel

theorem cycChk62 : zeroL (wordS e7T 133 [132, 125] [(132, 1)] ++ scale (-(1)) [(62, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk59
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk60
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk61
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk62
