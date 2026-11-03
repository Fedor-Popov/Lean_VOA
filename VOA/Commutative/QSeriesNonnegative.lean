/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Commutative.WeightedPolynomialHilbert
import VOA.Commutative.QMultiplicityProfile

/-! # Coefficient positivity for the literal Hilbert-bound summands -/
namespace VOA.QSeries
open scoped BigOperators
noncomputable section

/-- A rational formal series has nonnegative ordinary coefficients. -/
def NonnegativeCoefficients (f : PowerSeries ℚ) : Prop :=
  ∀ d, 0 ≤ PowerSeries.coeff d f

theorem nonnegativeCoefficients_one : NonnegativeCoefficients 1 := by
  intro d
  simp only [PowerSeries.coeff_one]
  split_ifs <;> norm_num

theorem nonnegativeCoefficients_X_pow (n : ℕ) :
    NonnegativeCoefficients ((PowerSeries.X : PowerSeries ℚ) ^ n) := by
  intro d
  simp only [PowerSeries.coeff_X_pow]
  split_ifs <;> norm_num

theorem NonnegativeCoefficients.mul {f g : PowerSeries ℚ}
    (hf : NonnegativeCoefficients f) (hg : NonnegativeCoefficients g) :
    NonnegativeCoefficients (f * g) := by
  intro d
  rw [PowerSeries.coeff_mul]
  exact Finset.sum_nonneg (fun ij _ => mul_nonneg (hf ij.1) (hg ij.2))

theorem NonnegativeCoefficients.prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℚ)
    (hf : ∀ i ∈ s, NonnegativeCoefficients (f i)) :
    NonnegativeCoefficients (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using nonnegativeCoefficients_one
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (hf i (Finset.mem_insert_self _ _)).mul
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- Reciprocal finite Euler products count actual finite weighted monomials. -/
theorem nonnegativeCoefficients_reciprocalQFactorial (n : ℕ) :
    NonnegativeCoefficients (reciprocalQFactorial n) := by
  intro d
  rw [← prod_weightedGeometric_eq_reciprocalQFactorial,
    coeff_prod_weightedGeometric_eq_card _ (fun i : Fin n => by omega)]
  exact Nat.cast_nonneg _

/-- All literal profile/residual summands are nonnegative, including beyond the
cutoffs used when comparing finite subsets of the Hilbert-bound source sum. -/
theorem nonnegativeCoefficients_multiplicityResidualTerm {m : ℕ}
    (r : Fin (m + 1) → ℕ) (s t c : ℕ) :
    NonnegativeCoefficients (multiplicityResidualTerm r s t c) := by
  unfold multiplicityResidualTerm
  exact ((((nonnegativeCoefficients_X_pow _).mul
    (NonnegativeCoefficients.prod Finset.univ _ (fun i _ =>
      nonnegativeCoefficients_reciprocalQFactorial (r i)))).mul
    (nonnegativeCoefficients_reciprocalQFactorial s)).mul
    (nonnegativeCoefficients_reciprocalQFactorial t)).mul
    (nonnegativeCoefficients_reciprocalQFactorial c)

end
end VOA.QSeries
