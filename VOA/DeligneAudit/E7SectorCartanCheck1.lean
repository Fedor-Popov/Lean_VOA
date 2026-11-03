/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorChecksDefs

/-! Small exact kernel-check pilot for the unchanged E7 sector predicate. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

open VOA.AffineGeneral.SCLie

set_option linter.style.longLine false

theorem cartan_ok_1_2 : (List.range' 1 1).all (fun h => (List.range 133).all fun y =>
    coef (entry e7T h y) 132 == if y = 132 then -((thetaH ⟨h % 133, Nat.mod_lt _ (by norm_num)⟩ : ℕ) : ℤ) else 0) = true := by
  decide +kernel

#print axioms cartan_ok_1_2

end VOA.DeligneAudit.DeligneCarrier.E7
