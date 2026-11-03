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

theorem cycChk51 : zeroL (wordS e7T 133 [132, 114] [(132, 1)] ++ scale (-(1)) [(51, 1)]) = true := by
  decide +kernel

theorem cycChk52 : zeroL (wordS e7T 133 [131, 119] [(132, 1)] ++ scale (-(-1)) [(52, 1)]) = true := by
  decide +kernel

theorem cycChk53 : zeroL (wordS e7T 133 [132, 116] [(132, 1)] ++ scale (-(1)) [(53, 1)]) = true := by
  decide +kernel

theorem cycChk54 : zeroL (wordS e7T 133 [132, 117] [(132, 1)] ++ scale (-(1)) [(54, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk51
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk52
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk53
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk54
