/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7LieForm
import VOA.DeligneAudit.E7CarrierTables
import VOA.DeligneAudit.E7Quad

/-!
# Kernel check: the cert Casimir is the inverse-form quadric `Σ Gi2ᵢⱼ XᵢXⱼ` (one sort)
-/

namespace VOA.DeligneAudit.E7Lie

open VOA.DeligneAudit.E7Sparse

/-- Twice the inverse form as a function. -/
def Gi2 (a b : Fin 133) : ℤ := ((Gi2L a).map fun t => if t.1 = b then t.2 else 0).sum

/-- `Σ_{i,j} Gi2ᵢⱼ XᵢXⱼ` as a sparse quadric. -/
def giList : List (ℕ × ℕ × ℤ) :=
  (List.finRange 133).flatMap fun i => (Gi2L i).map fun t => (i.val, t.1.val, t.2)

/-- **`Σ Gi2ᵢⱼ XᵢXⱼ = Q`** (the cert Casimir of `E7CarrierTables`). -/
theorem giList_eq_qQ : quadZero (giList ++ scaleQ (-1) DeligneCarrier.E7.qQ) = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie
