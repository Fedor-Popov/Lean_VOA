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

theorem cycChk91 : zeroL (wordS e7T 133 [123, 82] [(132, 1)] ++ scale (-(1)) [(91, 1)]) = true := by
  decide +kernel

theorem cycChk92 : zeroL (wordS e7T 133 [125, 76] [(132, 1)] ++ scale (-(1)) [(92, 1)]) = true := by
  decide +kernel

theorem cycChk93 : zeroL (wordS e7T 133 [128] [(132, 1)] ++ scale (-(-1)) [(93, 1)]) = true := by
  decide +kernel

theorem cycChk94 : zeroL (wordS e7T 133 [127] [(132, 1)] ++ scale (-(1)) [(94, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk91
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk92
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk93
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk94
