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

theorem cycChk15 : zeroL (wordS e7T 133 [129, 99] [(132, 1)] ++ scale (-(-1)) [(15, 1)]) = true := by
  decide +kernel

theorem cycChk16 : zeroL (wordS e7T 133 [130, 93] [(132, 1)] ++ scale (-(1)) [(16, 1)]) = true := by
  decide +kernel

theorem cycChk17 : zeroL (wordS e7T 133 [131, 88] [(132, 1)] ++ scale (-(-1)) [(17, 1)]) = true := by
  decide +kernel

theorem cycChk18 : zeroL (wordS e7T 133 [130, 94] [(132, 1)] ++ scale (-(1)) [(18, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk15
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk16
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk17
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk18
