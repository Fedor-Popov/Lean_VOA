/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8SectorDefs

/-!
# `E₈` coadjoint cyclicity: Boolean word checks `0..3` (depth 2 from `δ_{247}`, light imports)
-/

namespace VOA.DeligneAudit.DeligneCarrier.E8

open VOA.AffineGeneral.SCLie VOA.DeligneAudit.E6SectorSparse

set_option linter.style.longLine false

theorem cycChk0 : zeroL (([([241, 164], (-1 : ℤ)), ([240, 165], (1 : ℤ))] : List (List ℕ × ℤ)).flatMap (fun w => scale w.2 (wordS e8T 248 w.1 [(247, 1)])) ++
    scale (-(1)) [(0, 1)]) = true := by
  decide +kernel

theorem cycChk1 : zeroL (([([242, 157], (-1 : ℤ)), ([243, 150], (1 : ℤ)), ([244, 143], (-1 : ℤ)), ([245, 136], (1 : ℤ)), ([246, 128], (1 : ℤ)), ([247, 7], (-1 : ℤ)), ([240, 165], (-1 : ℤ))] : List (List ℕ × ℤ)).flatMap (fun w => scale w.2 (wordS e8T 248 w.1 [(247, 1)])) ++
    scale (-(2)) [(1, 1)]) = true := by
  decide +kernel

theorem cycChk2 : zeroL (([([240, 165], (1 : ℤ)), ([242, 157], (-1 : ℤ)), ([243, 150], (1 : ℤ)), ([244, 143], (-1 : ℤ)), ([245, 136], (1 : ℤ)), ([246, 128], (1 : ℤ)), ([247, 7], (-1 : ℤ))] : List (List ℕ × ℤ)).flatMap (fun w => scale w.2 (wordS e8T 248 w.1 [(247, 1)])) ++
    scale (-(2)) [(2, 1)]) = true := by
  decide +kernel

theorem cycChk3 : zeroL (([([243, 150], (1 : ℤ)), ([244, 143], (-1 : ℤ)), ([245, 136], (1 : ℤ)), ([246, 128], (1 : ℤ)), ([247, 7], (-1 : ℤ))] : List (List ℕ × ℤ)).flatMap (fun w => scale w.2 (wordS e8T 248 w.1 [(247, 1)])) ++
    scale (-(1)) [(3, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E8
