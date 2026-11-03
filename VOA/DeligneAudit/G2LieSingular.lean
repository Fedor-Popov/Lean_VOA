/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.G2LieData
import VOA.DeligneAudit.G2LieSingQ

/-!
# The weight-two singular vector of `V^{-5/3}(𝔤₂)`

`g2sv = -J^{2}_{-1}J^{2}_{-1}|0⟩ + 3 J^{5}_{-1}J^{9}_{-1}|0⟩ + 3 J^{6}_{-1}J^{10}_{-1}|0⟩`
(table basis of `g2CertData`). Its symbol `-X₂² + 3X₅X₉ + 3X₆X₁₀` is the relation `P₀` of
`I₂ⁿˢ = V(2ω₁)` (highest weight for the positive system, `G2SectorTables.relRaw[0]`). It is positive-mode singular at `k = -5/3` (kernel-checked
integer identities `g2_q1`, `g2_q2` through the rational-level criterion
`quadStateQ_mem_maxIdeal`), hence **`g2sv_mem_maxIdeal`** and **`g2sv_proj`**: it vanishes
in `L_{-5/3}(𝔤₂) = g2W`.

Numerics (outside Lean): the weight-two singular space at `k
= -5/3` is `27`-dimensional and contains `g2sv`.
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.G2Lie

open VOA.AffineGeneral VOA.AffineGeneral.SCLie

noncomputable section

/-- Integer structure constants of `g2T`. -/
def g2scZ (a b c : Fin 14) : ℤ := coef (entry g2T a b) c

/-- Integer form table `g2Gm`. -/
def g2fZ (a b : Fin 14) : ℤ := formV g2Gm [((a : ℕ), 1)] [((b : ℕ), 1)]

/-- The terms of the singular vector. -/
def g2svTerms : List (ℤ × Fin 14 × Fin 14) := [(-1, 2, 2), (3, 5, 9), (3, 6, 10)]

theorem g2_q1 : ∀ x g : Fin 14, q1Z g2scZ g2fZ (-5) 3 g2svTerms x g = 0 := by decide +kernel

theorem g2_q2 : ∀ x : Fin 14, q2Z g2scZ g2fZ (-5) g2svTerms x = 0 := by decide +kernel

theorem g2_level_eq : ((-5 : ℤ) : ℂ) / ((3 : ℤ) : ℂ) = (-5/3 : ℂ) := by push_cast; ring

/-- The singular vector. -/
def g2sv : Vacuum g2CertData (-5/3) :=
  quadState g2CertData (-5/3) (termsZC g2svTerms)

/-- **The singular vector lies in the maximal ideal.** -/
theorem g2sv_mem_maxIdeal : g2sv ∈ maxIdeal g2CertData (-5/3) g2_level_ne := by
  have key : ∀ (k : ℂ) (hk : k + g2CertData.h ≠ 0), k = ((-5 : ℤ) : ℂ) / ((3 : ℤ) : ℂ) →
      quadState g2CertData k (termsZC g2svTerms) ∈ maxIdeal g2CertData k hk := by
    intro k hk e
    subst e
    exact quadStateQ_mem_maxIdeal (D := g2CertData) (scZ := g2scZ) (fZ := g2fZ)
      (fun a b c => g2CertData_sc a b c) (fun a b => g2CertData_form a b) (-5) 3 (by norm_num)
      hk g2svTerms g2_q1 g2_q2
  exact key _ g2_level_ne g2_level_eq.symm

/-- **The singular vector vanishes in `L_{-5/3}(𝔤₂)`.** -/
theorem g2sv_proj : simpleProjection g2CertData (-5/3) g2_level_ne g2sv = 0 := by
  rw [simpleProjection, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact g2sv_mem_maxIdeal

end

end VOA.DeligneAudit.G2Lie

section AxiomAudit
#print axioms VOA.DeligneAudit.G2Lie.g2sv_mem_maxIdeal
#print axioms VOA.DeligneAudit.G2Lie.g2sv_proj
end AxiomAudit
