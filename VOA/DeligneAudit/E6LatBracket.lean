/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6LatBasis
import VOA.DeligneAudit.E6LatModel

/-!
# The `E₆` cert basis of `e6Lie`: the brackets

`bracket_xs`: **`⁅xs a, xs b⁆ = ∑ c, sZ a b c • xs c`**, the cert structure constants (`pairOK_all` and
`bracket_of_pairOK`), as in the `E7LieData`.
-/

namespace VOA.DeligneAudit.E6Lat

open VOA VOA.LatGen VOA.IntegralLattice VOA.CartanLattices VOA.AffineGeneral

noncomputable section

theorem bracket (a b : Fin 78) : ⁅xs a, xs b⁆ = spL (sL a b) :=
  bracket_of_pairOK a b (pairOK_all a b)

theorem spL_eq_sum (l : List (Fin 78 × ℤ)) :
    spL l = ∑ c, (((l.map fun t => if t.1 = c then t.2 else 0).sum : ℤ) : ℂ) • xs c := by
  induction l with
  | nil => simp [spL]
  | cons t l ih =>
      rw [spL, List.map_cons, List.sum_cons, ← spL, ih]
      simp only [List.map_cons, List.sum_cons, Int.cast_add, add_smul, Finset.sum_add_distrib,
        apply_ite (fun z : ℤ => (z : ℂ)), Int.cast_zero, ite_smul, zero_smul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]

/-- **The cert brackets in the lattice model.** -/
theorem bracket_xs (a b : Fin 78) : ⁅xs a, xs b⁆ = ∑ c, (sZ a b c : ℂ) • xs c := by
  rw [bracket, spL_eq_sum]
  rfl

end

end VOA.DeligneAudit.E6Lat
