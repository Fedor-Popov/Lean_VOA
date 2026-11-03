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

theorem cycChk99 : zeroL (wordS e7T 133 [126] [(132, 1)] ++ scale (-(1)) [(99, 1)]) = true := by
  decide +kernel

theorem cycChk100 : zeroL (wordS e7T 133 [125] [(132, 1)] ++ scale (-(-1)) [(100, 1)]) = true := by
  decide +kernel

theorem cycChk101 : zeroL (wordS e7T 133 [121, 76] [(132, 1)] ++ scale (-(1)) [(101, 1)]) = true := by
  decide +kernel

theorem cycChk102 : zeroL (wordS e7T 133 [120, 76] [(132, 1)] ++ scale (-(1)) [(102, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk99
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk100
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk101
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk102
