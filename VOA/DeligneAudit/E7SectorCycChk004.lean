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

theorem cycChk4 : zeroL (([([129, 88], (1 : ℤ)), ([130, 82], (-1 : ℤ)), ([131, 76], (-1 : ℤ)), ([132, 0], (-1 : ℤ)), ([127, 94], (1 : ℤ))] : List (List ℕ × ℤ)).flatMap (fun w => scale w.2 (wordS e7T 133 w.1 [(132, 1)])) ++
    scale (-(2)) [(4, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk4
