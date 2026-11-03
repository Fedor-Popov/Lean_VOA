/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.PolynomialLeadingSymbol
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Signed minimum-weight filtration on polynomials

Integer lower bounds avoid truncated subtraction when an annihilation
operator differentiates a variable of larger weight. Multiplication
adds lower bounds, and a partial derivative subtracts exactly the weight
of its variable as a bound. Zero derivatives satisfy every bound.
-/
namespace VOA.PolynomialMinimum
noncomputable section
open MvPolynomial
open Classical
open scoped BigOperators
variable {σ : Type*}

/-- Span of the monomials whose signed weight is at least d. -/
def AtLeast (w : σ → ℤ) (d : ℤ) : Submodule ℂ (MvPolynomial σ ℂ) :=
  Submodule.span ℂ {P | ∃ e : σ →₀ ℕ, d ≤ Finsupp.weight w e ∧ P = monomial e 1}

/-- A monomial belongs whenever its weight satisfies the bound. -/
theorem monomial_mem {w : σ → ℤ} {d : ℤ} (e : σ →₀ ℕ)
    (h : d ≤ Finsupp.weight w e) : monomial e (1 : ℂ) ∈ AtLeast w d :=
  Submodule.subset_span ⟨e,h,rfl⟩

/-- Increasing the required lower bound gives a smaller submodule. -/
theorem mono {w : σ → ℤ} {d e : ℤ} (h : d ≤ e) : AtLeast w e ≤ AtLeast w d := by
  apply Submodule.span_mono
  rintro P ⟨u,hu,rfl⟩
  exact ⟨u,h.trans hu,rfl⟩

/-- The span definition is equivalent to a bound on every nonzero
coefficient; no finiteness of the variable set is required. -/
theorem mem_iff {w : σ → ℤ} {d : ℤ} (P : MvPolynomial σ ℂ) :
    P ∈ AtLeast w d ↔ ∀ e, coeff e P ≠ 0 → d ≤ Finsupp.weight w e := by
  constructor
  · intro hp
    induction hp using Submodule.span_induction with
    | mem P hp =>
      obtain ⟨u,hu,rfl⟩ := hp
      intro e he
      by_cases hue : u=e
      · simpa [← hue] using hu
      · simp [coeff_monomial, hue] at he
    | zero => simp
    | add P Q _ _ hp hq =>
      intro e he
      by_cases h : coeff e P=0
      · exact hq e (by simpa [coeff_add,h] using he)
      · exact hp e h
    | smul c P _ hp =>
      intro e he
      exact hp e (right_ne_zero_of_mul (by simpa [coeff_smul] using he))
  · intro hp
    rw [MvPolynomial.as_sum P]
    apply Submodule.sum_mem
    intro e he
    have hm := (AtLeast w d).smul_mem (coeff e P)
      (monomial_mem e (hp e (mem_support_iff.mp he)))
    simpa [smul_monomial] using hm

/-- Multiplying two polynomials adds their minimum-weight bounds. -/
theorem mul_mem {w : σ → ℤ} {d e : ℤ} {P Q : MvPolynomial σ ℂ}
    (hp : P ∈ AtLeast w d) (hq : Q ∈ AtLeast w e) : P*Q ∈ AtLeast w (d+e) := by
  rw [mem_iff] at hp hq ⊢
  intro u hu
  rw [coeff_mul] at hu
  obtain ⟨⟨a,b⟩,hab,ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu
  rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hab,map_add]
  exact add_le_add (hp a (left_ne_zero_of_mul ht)) (hq b (right_ne_zero_of_mul ht))

/-- Creation raises the bound by the variable's signed weight. -/
theorem X_mul_mem {w : σ → ℤ} (v : σ) {d : ℤ} {P : MvPolynomial σ ℂ}
    (hp : P ∈ AtLeast w d) : X v * P ∈ AtLeast w (d+w v) := by
  have hx : (X v : MvPolynomial σ ℂ) ∈ AtLeast w (w v) := by
    apply monomial_mem
    simp [Finsupp.weight_single]
  simpa [add_comm] using mul_mem hx hp

/-- Partial differentiation lowers the bound by the differentiated
variable's weight, without natural-number truncation. -/
theorem pderiv_mem {w : σ → ℤ} (v : σ) {d : ℤ} {P : MvPolynomial σ ℂ}
    (hp : P ∈ AtLeast w d) : pderiv v P ∈ AtLeast w (d-w v) := by
  induction hp using Submodule.span_induction with
  | mem P hp =>
    obtain ⟨e,he,rfl⟩ := hp
    rw [pderiv_monomial,one_mul]
    by_cases hv : e v=0
    · simp [hv]
    · have hw := Finsupp.weight_sub_single_add (w := w) hv
      have hm := monomial_mem (e-Finsupp.single v 1) (show d-w v ≤
          Finsupp.weight w (e-Finsupp.single v 1) by omega)
      simpa [smul_monomial] using (AtLeast w (d-w v)).smul_mem (e v : ℂ) hm
  | zero => simp
  | add P Q _ _ hp hq => simpa using (AtLeast w (d-w v)).add_mem hp hq
  | smul c P _ hp => simpa using (AtLeast w (d-w v)).smul_mem c hp

/-- A homogeneous polynomial satisfies its exact signed lower bound. -/
theorem homogeneous_mem {w : σ → ℤ} {d : ℤ} {P : MvPolynomial σ ℂ}
    (hp : P.IsWeightedHomogeneous w d) : P ∈ AtLeast w d :=
  (mem_iff P).mpr fun e he => (hp he).ge

/-- Components strictly below a valid minimum weight vanish. -/
theorem component_below {w : σ → ℤ} {d e : ℤ} {P : MvPolynomial σ ℂ}
    (hp : P ∈ AtLeast w d) (he : e<d) : weightedHomogeneousComponent w e P=0 := by
  ext u
  simp only [coeff_weightedHomogeneousComponent,coeff_zero]
  split_ifs with hu
  · by_contra hc
    exact (not_le_of_gt he) (hu ▸ (mem_iff P).mp hp u hc)
  · rfl

end
end VOA.PolynomialMinimum
