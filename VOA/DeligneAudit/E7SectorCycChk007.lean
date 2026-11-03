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

theorem cycChk7 : zeroL (wordS e7T 133 [126, 103] [(132, 1)] ++ scale (-(-1)) [(7, 1)]) = true := by
  decide +kernel

theorem cycChk8 : zeroL (wordS e7T 133 [128, 99] [(132, 1)] ++ scale (-(1)) [(8, 1)]) = true := by
  decide +kernel

theorem cycChk9 : zeroL (wordS e7T 133 [129, 93] [(132, 1)] ++ scale (-(-1)) [(9, 1)]) = true := by
  decide +kernel

theorem cycChk10 : zeroL (wordS e7T 133 [130, 88] [(132, 1)] ++ scale (-(1)) [(10, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk7
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk8
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk9
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk10
