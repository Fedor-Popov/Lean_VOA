/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6SectorChecks

set_option linter.style.longLine false

/-!
# E₆ sector data: Boolean table checks (light imports)
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneCarrier.E6

open VOA.DeligneAudit.E6Sparse VOA.AffineGeneral.SCLie

theorem raising_ok : (List.range' 6 36).all (fun e => (List.range 78).all fun y => coef (entry e6T e y) 77 == 0) = true := by
  decide +kernel

theorem cartan_ok : (List.range 6).all (fun h => (List.range 78).all fun y =>
    coef (entry e6T h y) 77 == if y = 77 then -((thetaH ⟨h % 78, Nat.mod_lt _ (by norm_num)⟩ : ℕ) : ℤ) else 0) = true := by
  decide +kernel


end VOA.DeligneAudit.DeligneCarrier.E6
