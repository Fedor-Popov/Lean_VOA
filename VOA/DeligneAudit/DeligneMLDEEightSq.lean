/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import VOA.DeligneAudit.DeligneCharacterTypes

/-!
# `E₄² = E₈` as a formal `q`-series identity over `ℚ`

The heat-equation identity of `DeligneMLDEHeat` yields one relation per weight; at weight eight
it gives `2θE₆ = E₂E₆ - E₈`.  To reach Ramanujan's `2θE₆ = E₂E₆ - E₄²` one needs `E₄² = E₈`,
which is a one-line consequence of Mathlib's level-one **Sturm bound**
(`ModularForm.sturm_bound_levelOne_nat`): `E₄² - E₈` is a weight-8 level-one modular form with
vanishing constant term.  The coefficients are Mathlib's `EisensteinSeries.E_qExpansion_coeff`.

Main result: `eight_sq` — for every `n`,
`∑_{i+j=n} e₄(i) e₄(j) = e₈(n)` with `e₄ = 1, 240σ₃(n)` and `e₈ = 1, 480σ₇(n)`.
-/

namespace VOA.DeligneAudit.DeligneMLDE.EightSq

open ModularForm EisensteinSeries UpperHalfPlane ModularFormClass MatrixGroups

noncomputable section

/-- `E₈` as a level-one modular form. -/
abbrev E₈ : ModularForm 𝒮ℒ 8 := E (by norm_num : 3 ≤ 8)

/-- `E₄² - E₈`, of weight 8. -/
def diffForm : ModularForm 𝒮ℒ 8 := ModularForm.mcast (by decide) (E₄.pow 2) - E₈

theorem diffForm_qExpansion :
    qExpansion 1 diffForm = qExpansion 1 E₄ * qExpansion 1 E₄ - qExpansion 1 E₈ := by
  simp only [diffForm, coe_sub, coe_mcast,
    ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  ring

theorem diffForm_eq_zero : diffForm = 0 := by
  apply sturm_bound_levelOne_nat (k := 8)
  have h0 : (qExpansion 1 diffForm).coeff 0 = 0 := by
    rw [diffForm_qExpansion]
    simp [PowerSeries.coeff_mul, -PowerSeries.coeff_zero_eq_constantCoeff,
      E_qExpansion_coeff_zero _ ⟨2, rfl⟩, E_qExpansion_coeff_zero (k := 8) (by norm_num) ⟨4, rfl⟩]
  have hne : (qExpansion 1 diffForm).order ≠ 0 :=
    PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mpr (by simpa using h0)
  norm_num
  exact pos_iff_ne_zero.mpr hne

/-- `qE₄² = qE₈` as power series over `ℂ`. -/
theorem qExpansion_E4_sq : qExpansion 1 E₄ * qExpansion 1 E₄ = qExpansion 1 E₈ := by
  have h : qExpansion 1 diffForm = 0 := by
    rw [ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods_SL]
    exact diffForm_eq_zero
  rw [diffForm_qExpansion] at h
  exact sub_eq_zero.mp h

/-- `e₄(n)`. -/
def e4 (n : ℕ) : ℚ := if n = 0 then 1 else 240 * DeligneCharacter.sigmaK 3 n
/-- `e₈(n)`. -/
def e8 (n : ℕ) : ℚ := if n = 0 then 1 else 480 * DeligneCharacter.sigmaK 7 n

theorem sigma_eq_sigmaK (k n : ℕ) :
    (ArithmeticFunction.sigma k n : ℂ) = ((DeligneCharacter.sigmaK k n : ℚ) : ℂ) := by
  rw [ArithmeticFunction.sigma_apply, DeligneCharacter.sigmaK]; push_cast; rfl

theorem coeff_E4 (n : ℕ) : (qExpansion 1 E₄).coeff n = ((e4 n : ℚ) : ℂ) := by
  rw [E_qExpansion_coeff _ ⟨2, rfl⟩, e4]
  split_ifs with h
  · simp
  · rw [show bernoulli 4 = -1 / 30 by decide +kernel, sigma_eq_sigmaK]; push_cast; ring

theorem coeff_E8 (n : ℕ) : (qExpansion 1 E₈).coeff n = ((e8 n : ℚ) : ℂ) := by
  rw [E_qExpansion_coeff _ ⟨4, rfl⟩, e8]
  split_ifs with h
  · simp
  · rw [show bernoulli 8 = -1 / 30 by decide +kernel, sigma_eq_sigmaK]; push_cast; ring

/-- **`E₄² = E₈`, coefficientwise over `ℚ`.** -/
theorem eight_sq (n : ℕ) :
    ∑ p ∈ Finset.antidiagonal n, e4 p.1 * e4 p.2 = e8 n := by
  have h := congrArg (fun F => PowerSeries.coeff n F) qExpansion_E4_sq
  simp only [PowerSeries.coeff_mul, coeff_E4, coeff_E8] at h
  exact_mod_cast h

end

end VOA.DeligneAudit.DeligneMLDE.EightSq

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneMLDE.EightSq.eight_sq
end AxiomAudit
