/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Minimum weighted degree in a multivariable polynomial ideal

This file packages the elementary support argument that an ideal generated in weighted degrees
at least `D` has `d`th power supported in weighted degrees at least `d * D`.  It is useful for
proving that an adic filtration separates on a fixed homogeneous polynomial piece.
-/

namespace VOA.MvPolynomialMinimumWeight

open scoped BigOperators

noncomputable section

universe uσ uR

variable {σ : Type uσ} {R : Type uR} [CommSemiring R]

/-- Polynomials whose every supported monomial has weighted degree at least `n`. -/
def minimumWeightIdeal (w : σ → ℕ) (n : ℕ) : Ideal (MvPolynomial σ R) := by
  classical
  refine
    { carrier := {p | ∀ d ∈ p.support, n ≤ Finsupp.weight w d}
      zero_mem' := by simp
      add_mem' := ?_
      smul_mem' := ?_ }
  · intro p q hp hq d hd
    have hd' := MvPolynomial.support_add hd
    rw [Finset.mem_union] at hd'
    exact hd'.elim (hp d) (hq d)
  · intro a p hp d hd
    have hd' := MvPolynomial.support_mul a p hd
    rw [Finset.mem_add] at hd'
    rcases hd' with ⟨u, hu, v, hv, huv⟩
    subst d
    have hmin := hp v hv
    rw [map_add]
    omega

@[simp]
theorem mem_minimumWeightIdeal_iff {w : σ → ℕ} {n : ℕ} {p : MvPolynomial σ R} :
    p ∈ minimumWeightIdeal w n ↔ ∀ d ∈ p.support, n ≤ Finsupp.weight w d :=
  Iff.rfl

/-- Requiring a larger minimum degree gives a smaller ideal. -/
theorem minimumWeightIdeal_antitone (w : σ → ℕ) :
    Antitone (minimumWeightIdeal (R := R) w) := by
  intro m n hmn p hp d hd
  exact hmn.trans (hp d hd)

/-- The minimum-degree-zero ideal is the whole polynomial ring. -/
@[simp]
theorem minimumWeightIdeal_zero (w : σ → ℕ) :
    minimumWeightIdeal (R := R) w 0 = ⊤ := by
  apply top_unique
  intro p _ d hd
  exact Nat.zero_le _

/-- Multiplying polynomials adds their lower weighted-degree bounds. -/
theorem mul_mem_minimumWeightIdeal {w : σ → ℕ} {m n : ℕ}
    {p q : MvPolynomial σ R}
    (hp : p ∈ minimumWeightIdeal w m)
    (hq : q ∈ minimumWeightIdeal w n) :
    p * q ∈ minimumWeightIdeal w (m + n) := by
  classical
  intro d hd
  have hd' := MvPolynomial.support_mul p q hd
  rw [Finset.mem_add] at hd'
  rcases hd' with ⟨u, hu, v, hv, huv⟩
  subst d
  have hpu := hp u hu
  have hqv := hq v hv
  rw [map_add]
  omega

/-- The product of two minimum-degree ideals has the sum lower bound. -/
theorem minimumWeightIdeal_mul_le (w : σ → ℕ) (m n : ℕ) :
    minimumWeightIdeal (R := R) w m * minimumWeightIdeal w n ≤
      minimumWeightIdeal w (m + n) := by
  rw [Ideal.mul_le]
  intro p hp q hq
  exact mul_mem_minimumWeightIdeal hp hq

/-- Powers of an ideal generated above degree `D` have minimum degree `d * D`. -/
theorem ideal_pow_le_minimumWeightIdeal (w : σ → ℕ) (D : ℕ)
    (I : Ideal (MvPolynomial σ R))
    (hI : I ≤ minimumWeightIdeal w D) (d : ℕ) :
    I ^ d ≤ minimumWeightIdeal w (d * D) := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [pow_succ']
      exact (Ideal.mul_mono hI ih).trans (by
        simpa only [Nat.succ_mul, Nat.add_comm] using minimumWeightIdeal_mul_le
          (R := R) w D (d * D))

/-- A homogeneous polynomial strictly below a support lower bound is zero. -/
theorem eq_zero_of_isWeightedHomogeneous_of_mem_minimumWeightIdeal
    {w : σ → ℕ} {m n : ℕ} {p : MvPolynomial σ R}
    (hp : p.IsWeightedHomogeneous w m)
    (hmem : p ∈ minimumWeightIdeal w n) (hmn : m < n) : p = 0 := by
  apply MvPolynomial.ext
  intro d
  by_cases hd : MvPolynomial.coeff d p = 0
  · exact hd
  · have hweight := hp hd
    have hmin := hmem d (MvPolynomial.mem_support_iff.mpr hd)
    omega

end

end VOA.MvPolynomialMinimumWeight

section AxiomAudit
namespace VOA.MvPolynomialMinimumWeight
#print axioms minimumWeightIdeal_mul_le
#print axioms ideal_pow_le_minimumWeightIdeal
#print axioms eq_zero_of_isWeightedHomogeneous_of_mem_minimumWeightIdeal
end VOA.MvPolynomialMinimumWeight
end AxiomAudit
