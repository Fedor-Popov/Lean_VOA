/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroScreeningFock

/-!
# Exact factorial cancellation in screening coefficients

Adding one oscillator multiplies the denominator by its energy and its
new multiplicity. This finite identity is what turns differentiating the
screening polynomial into inserting a power sum in its residue.
-/
namespace VOA.VirasoroScreening
open scoped BigOperators

/-- The positive mode and factorial denominator of a single occupation. -/
noncomputable def screeningDenominator (d : ℕ →₀ ℕ) : ℚ :=
  d.prod (fun i n => ((i+1:ℕ):ℚ)^n * (Nat.factorial n : ℚ))

/-- Every denominator factor is a positive integer, hence the product is nonzero. -/
theorem screeningDenominator_ne_zero (d : ℕ →₀ ℕ) : screeningDenominator d ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact mul_ne_zero (pow_ne_zero _ (by positivity)) (by positivity)

/-- Adding one oscillator multiplies the denominator by its energy and its
new multiplicity, also when that oscillator was absent before. -/
theorem screeningDenominator_add_single (d : ℕ →₀ ℕ) (i : ℕ) :
    screeningDenominator (d + Finsupp.single i 1) =
      screeningDenominator d * ((i+1:ℕ):ℚ) * ((d i+1:ℕ):ℚ) := by
  classical
  let g : ℕ → ℕ → ℚ := fun j n => ((j+1:ℕ):ℚ)^n * (Nat.factorial n : ℚ)
  have hg : ∀ j, g j 0 = 1 := by intro j; simp [g]
  have h0 := Finsupp.mul_prod_erase' d i g hg
  have h1 := Finsupp.mul_prod_erase' (d + Finsupp.single i 1) i g hg
  change g i (d i) * (d.erase i).prod g = screeningDenominator d at h0
  change g i ((d + Finsupp.single i 1 : ℕ →₀ ℕ) i) *
    ((d + Finsupp.single i 1).erase i).prod g =
      screeningDenominator (d + Finsupp.single i 1) at h1
  rw [← h1, ← h0]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.erase_add,
    Finsupp.erase_single, if_pos rfl, add_zero]
  dsimp [g]
  rw [pow_succ, Nat.factorial_succ]
  push_cast
  ring

/-- The exact cancellation needed by a first oscillator derivative.
No division by beta is used, so the identity also holds at beta zero. -/
theorem screeningPrefactor_add_single (β : ℚ) (d : ℕ →₀ ℕ) (i : ℕ) :
    (((i+1:ℕ):ℚ) * ((d i+1:ℕ):ℚ)) *
      screeningPrefactor β (d + Finsupp.single i 1) = β * screeningPrefactor β d := by
  classical
  have hs : (d + Finsupp.single i 1).sum (fun _ n => n) = d.sum (fun _ n => n) + 1 := by
    rw [Finsupp.sum_add_index (by simp) (by intros; rfl)]
    simp
  change _ * (β^((d + Finsupp.single i 1).sum fun _ n => n) /
    screeningDenominator (d + Finsupp.single i 1)) =
      β * (β^(d.sum fun _ n => n) / screeningDenominator d)
  rw [hs, screeningDenominator_add_single, pow_succ]
  have hd := screeningDenominator_ne_zero d
  have hi : ((i+1:ℕ):ℚ) ≠ 0 := by positivity
  have hdi : ((d i+1:ℕ):ℚ) ≠ 0 := by positivity
  field_simp
  <;> ring

/-- Coefficient extraction commutes with a partial derivative by shifting
one occupation up and multiplying by its new multiplicity. -/
theorem screening_pderiv_coeff {σ : Type*} (i : σ) (d : σ →₀ ℕ)
    (P : MvPolynomial σ ℂ) :
    MvPolynomial.coeff d (MvPolynomial.pderiv i P) =
      ((d i+1:ℕ):ℂ) * MvPolynomial.coeff (d + Finsupp.single i 1) P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, MvPolynomial.coeff_add, hP, hQ, mul_add]
  | monomial m c =>
    rw [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial,
      MvPolynomial.coeff_monomial]
    by_cases hm : m i=0
    · have he : m ≠ d + Finsupp.single i 1 := by
        intro he
        have hh := congrArg (fun e => e i) he
        simp [hm] at hh
      simp [hm, he]
    · have hr : m - Finsupp.single i 1 + Finsupp.single i 1 = m := by
        ext j
        by_cases hj : j=i
        · subst j; simp; omega
        · simp [hj]
      have he : m - Finsupp.single i 1 = d ↔ m = d + Finsupp.single i 1 := by
        constructor
        · intro h; rw [← hr, h]
        · intro h; rw [h, add_tsub_cancel_right]
      simp only [he]
      by_cases h : m = d + Finsupp.single i 1
      · subst m; simp [mul_comm]
      · simp [h]

end VOA.VirasoroScreening
