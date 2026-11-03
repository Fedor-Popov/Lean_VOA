/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8SectorDefs

/-!
# `E₈` coadjoint cyclicity: Boolean word checks `4..7` (depth 2 from `δ_{247}`, light imports)
-/

namespace VOA.DeligneAudit.DeligneCarrier.E8

open VOA.AffineGeneral.SCLie VOA.DeligneAudit.E6SectorSparse

set_option linter.style.longLine false

theorem cycChk4 : zeroL (([([244, 143], (-1 : ℤ)), ([245, 136], (1 : ℤ)), ([246, 128], (1 : ℤ)), ([247, 7], (-1 : ℤ))] : List (List ℕ × ℤ)).flatMap (fun w => scale w.2 (wordS e8T 248 w.1 [(247, 1)])) ++
    scale (-(1)) [(4, 1)]) = true := by
  decide +kernel

theorem cycChk5 : zeroL (([([245, 136], (1 : ℤ)), ([246, 128], (1 : ℤ)), ([247, 7], (-1 : ℤ))] : List (List ℕ × ℤ)).flatMap (fun w => scale w.2 (wordS e8T 248 w.1 [(247, 1)])) ++
    scale (-(1)) [(5, 1)]) = true := by
  decide +kernel

theorem cycChk6 : zeroL (([([246, 128], (1 : ℤ)), ([247, 7], (-1 : ℤ))] : List (List ℕ × ℤ)).flatMap (fun w => scale w.2 (wordS e8T 248 w.1 [(247, 1)])) ++
    scale (-(1)) [(6, 1)]) = true := by
  decide +kernel

theorem cycChk7 : zeroL (wordS e8T 248 [247] [(247, 1)] ++ scale (-(-1)) [(7, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E8
