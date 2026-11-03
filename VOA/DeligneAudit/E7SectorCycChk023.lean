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

theorem cycChk23 : zeroL (wordS e7T 133 [130, 100] [(132, 1)] ++ scale (-(1)) [(23, 1)]) = true := by
  decide +kernel

theorem cycChk24 : zeroL (wordS e7T 133 [131, 94] [(132, 1)] ++ scale (-(-1)) [(24, 1)]) = true := by
  decide +kernel

theorem cycChk25 : zeroL (wordS e7T 133 [132, 88] [(132, 1)] ++ scale (-(1)) [(25, 1)]) = true := by
  decide +kernel

theorem cycChk26 : zeroL (wordS e7T 133 [130, 103] [(132, 1)] ++ scale (-(1)) [(26, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk23
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk24
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk25
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk26
