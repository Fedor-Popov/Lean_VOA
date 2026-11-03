/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneFusionFiniteG
import VOA.DeligneAudit.DeligneSectorA2

/-!
# The finiteness clause for `A₂` in the type-generic form

One certificate step: `[f₁, f₂] = -f_θ` and `[f₁, f_θ] = 0`, so `f_θ` is nilpotent on `w`
(`top_nil` with `q = 1`; the `ftheta_pow` route via `heis_nilpotent` is not needed).

`a2_finiteTable : FiniteTableG A2sector`,
`a2_fusionTotalBoundG_of_dim : FusionTotalDimG A2sector → FusionTotalBoundG A2sector`.
-/

namespace VOA.DeligneAudit.FiniteG.A2

open VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.UnivG VOA.AffineSl3

/-- Raising letters and simple lowering letters. -/
def a2Kn (c : Fin 8) : Bool := decide (c.val < 3) || decide (c = 3 ∨ c = 4)

/-- The one nonzero structure constant used. -/
def a2Fnz (a b c : Fin 8) : Bool := decide (a = 3 ∧ b = 4 ∧ c = 5)

theorem a2_fnz : ∀ a b c, a2Fnz a b c = true → A2sector.f a b c ≠ 0 := by
  intro a b c h
  simp only [a2Fnz, decide_eq_true_eq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  change bracketTable 3 4 5 ≠ 0
  simp [bracketTable]

/-- The certificate. -/
def a2Cert : List (Step 8) := [(3, 4, [5])]

theorem a2_certValid : certValid A2sector.wt a2Fnz a2Kn a2Cert = true := by decide +kernel

theorem a2_cov : ∀ c : Fin 8, (certKnown a2Kn a2Cert c && !wEqB (A2sector.wt c) 0) = true ∨
    A2sector.raising c ∨ A2sector.cartan c ∨ A2sector.cartanN c := by
  change ∀ c : Fin 8, (certKnown a2Kn a2Cert c && !wEqB (wt2 c) 0) = true ∨
    (c.val < 3) ∨ (6 ≤ c.val) ∨ False
  decide +kernel

theorem a2_kn : ∀ c : Fin 8, a2Kn c = true → A2sector.raising c ∨ A2sector.lowering c := by
  change ∀ c : Fin 8, a2Kn c = true → (c.val < 3) ∨ (c = 3 ∨ c = 4)
  intro c h
  simpa [a2Kn] using h

/-- **The finiteness table facts for `A₂`.** -/
theorem a2_finiteTable : FiniteTableG A2sector :=
  finiteTableG_of_cert a2_fnz a2Kn a2Cert a2_kn a2_certValid a2_cov

/-- **`FusionTotalBoundG A2sector` reduces to the bare dimension bound.** -/
theorem a2_fusionTotalBoundG_of_dim (h : FusionTotalDimG A2sector) :
    FusionTotalBoundG A2sector :=
  fusionTotalBoundG_of_dim a2_finiteTable h

end VOA.DeligneAudit.FiniteG.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.FiniteG.A2.a2_finiteTable
#print axioms VOA.DeligneAudit.FiniteG.A2.a2_fusionTotalBoundG_of_dim
end AxiomAudit
