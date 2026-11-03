/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Commutative.QBinomialResidual
import VOA.Commutative.SymmetricWeightedDegree

/-! # Positive weighted polynomial Hilbert series as actual formal products -/
namespace VOA.QSeries
open scoped BigOperators
noncomputable section
variable {R I : Type*} [CommRing R]

/-- The actual geometric series in the positive-degree monomial X^A. -/
def weightedGeometric (A : ℕ) : PowerSeries R := powerShiftSum A (fun _ => 1)

/-- The positive geometric series is the inverse of its linear factor. -/
theorem one_sub_pow_mul_weightedGeometric (A : ℕ) (hA : 0 < A) :
    (1 - PowerSeries.X ^ A) * weightedGeometric (R := R) A = 1 := by
  have he := powerShiftSum_succ (R := R) A hA (fun _ => 1)
  change weightedGeometric A = 1 + PowerSeries.X ^ A * weightedGeometric A at he
  linear_combination he

/-- A geometric series has a finite sum valid through any requested degree. -/
theorem truncEq_weightedGeometric (A : ℕ) (hA : 0 < A) (d : ℕ) :
    TruncEq d (weightedGeometric (R := R) A)
      (∑ j : Fin (d + 1), PowerSeries.X ^ (A * j.val)) := by
  intro i hi
  rw [weightedGeometric, coeff_powerShiftSum A hA _ i d hi]
  simp only [mul_one]
  rw [Fin.sum_univ_eq_sum_range (fun j => (PowerSeries.X : PowerSeries R) ^ (A * j))]

/-- Coefficient agreement is preserved by finite products. -/
theorem TruncEq.prod {d : ℕ} {f g : I → PowerSeries R} (s : Finset I)
    (h : ∀ i ∈ s, TruncEq d (f i) (g i)) :
    TruncEq d (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact TruncEq.refl _ _
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- The degree-d coefficient of a weighted geometric product counts bounded
exponent vectors of exactly the required weighted sum. -/
theorem coeff_prod_weightedGeometric [Fintype I] (w : I → ℕ)
    (hw : ∀ i, 0 < w i) (d : ℕ) :
    PowerSeries.coeff d (∏ i, weightedGeometric (R := R) (w i)) =
      (Nat.card {e : I → Fin (d + 1) // ∑ i, w i * (e i).val = d} : R) := by
  classical
  rw [TruncEq.prod Finset.univ (fun i _ => truncEq_weightedGeometric (w i) (hw i) d) d le_rfl]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_pow_eq_pow_sum, map_sum, PowerSeries.coeff_X_pow]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_boole, eq_comm]

/-- The finite-function formula for the positive weighted degree. -/
theorem weight_eq_univ_sum [Fintype I] (w : I → ℕ) (e : I →₀ ℕ) :
    Finsupp.weight w e = ∑ i, w i * e i := by
  rw [Finsupp.weight_apply]
  rw [Finsupp.sum_fintype]
  · simp [Nat.mul_comm]
  · intro i; simp

/-- Positivity bounds every exponent by the total degree, so the finite
cube count is exactly the full weighted-monomial count. -/
def boundedWeightFiberEquiv [Fintype I] (w : I → ℕ) (hw : ∀ i, 0 < w i) (d : ℕ) :
    {e : I → Fin (d + 1) // ∑ i, w i * (e i).val = d} ≃
      {e : I →₀ ℕ // Finsupp.weight w e = d} where
  toFun e := ⟨Finsupp.equivFunOnFinite.symm (fun i => (e.val i).val), by
    simpa only [weight_eq_univ_sum, Finsupp.equivFunOnFinite_symm_apply_apply] using e.property⟩
  invFun e := ⟨fun i => ⟨e.val i, by
    have hb := Finsupp.le_weight w (Nat.ne_of_gt (hw i)) e.val
    rw [e.property] at hb
    omega⟩, by simpa only [← weight_eq_univ_sum] using e.property⟩
  left_inv e := by apply Subtype.ext; funext i; apply Fin.ext; rfl
  right_inv e := by apply Subtype.ext; ext i; rfl

/-- The geometric-factor product counts all monomials of positive weighted
degree, with no artificial cutoff in the resulting statement. -/
theorem coeff_prod_weightedGeometric_eq_card [Fintype I] (w : I → ℕ)
    (hw : ∀ i, 0 < w i) (d : ℕ) :
    PowerSeries.coeff d (∏ i, weightedGeometric (R := R) (w i)) =
      (Nat.card {e : I →₀ ℕ // Finsupp.weight w e = d} : R) := by
  classical
  rw [coeff_prod_weightedGeometric w hw d]
  exact congrArg (fun m : ℕ => (m : R)) (Nat.card_congr (boundedWeightFiberEquiv w hw d))

/-- The product with weights 1,...,n is the actual reciprocal q-factorial. -/
theorem prod_weightedGeometric_eq_reciprocalQFactorial (n : ℕ) :
    (∏ i : Fin n, weightedGeometric (R := R) (i.val + 1)) = reciprocalQFactorial n := by
  have hm : qFactorial PowerSeries.X n *
      (∏ i : Fin n, weightedGeometric (R := R) (i.val + 1)) = 1 := by
    rw [qFactorial_eq_prod, ← Fin.prod_univ_eq_prod_range
      (fun j => 1 - (PowerSeries.X : PowerSeries R) ^ (j + 1))]
    rw [← Finset.prod_mul_distrib]
    calc
      _ = ∏ _i : Fin n, (1 : PowerSeries R) := Finset.prod_congr rfl
        (fun i _ => one_sub_pow_mul_weightedGeometric (i.val + 1) (by omega))
      _ = 1 := Finset.prod_const_one
  calc
    _ = (qFactorial PowerSeries.X n * reciprocalQFactorial n) *
        (∏ i : Fin n, weightedGeometric (R := R) (i.val + 1)) := by
      rw [qFactorial_mul_reciprocal, one_mul]
    _ = reciprocalQFactorial n * (qFactorial PowerSeries.X n *
        (∏ i : Fin n, weightedGeometric (R := R) (i.val + 1))) := by ring
    _ = _ := by rw [hm, mul_one]

/-- Exact ordinary symmetric-polynomial Hilbert coefficients. The left
side is the actual vector-space dimension, and the right is a q-factorial. -/
theorem symmetricPiece_finrank_eq_coeff {K : Type*} [Field K] [Fintype I] (n : ℕ)
    (hn : Fintype.card I = n) (d : ℕ) :
    (Module.finrank K (SymmetricWeightedDegree.symmetricPiece (K := K) (I := I) d) : ℚ) =
      PowerSeries.coeff d (reciprocalQFactorial n : PowerSeries ℚ) := by
  rw [SymmetricWeightedDegree.symmetricPiece_finrank n hn d,
    ← prod_weightedGeometric_eq_reciprocalQFactorial,
    coeff_prod_weightedGeometric_eq_card _ (fun i => by omega)]

end
end VOA.QSeries
