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

theorem cycChk63 : zeroL (wordS e7T 133 [132, 126] [(132, 1)] ++ scale (-(1)) [(63, 1)]) = true := by
  decide +kernel

theorem cycChk64 : zeroL (wordS e7T 133 [132, 127] [(132, 1)] ++ scale (-(1)) [(64, 1)]) = true := by
  decide +kernel

theorem cycChk65 : zeroL (wordS e7T 133 [132, 128] [(132, 1)] ++ scale (-(1)) [(65, 1)]) = true := by
  decide +kernel

theorem cycChk66 : zeroL (wordS e7T 133 [132, 129] [(132, 1)] ++ scale (-(1)) [(66, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk63
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk64
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk65
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk66
