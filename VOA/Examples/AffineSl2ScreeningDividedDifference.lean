/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ScreeningSupport
import Mathlib.Algebra.Ring.GeomSum

/-!
# Finite beta divided differences without denominators

The beta factors are the actual auxiliary polynomials used by the screening
candidate. Their divided differences are finite geometric sums, so the
identities remain valid even when two auxiliary variables coincide.
-/
namespace VOA.Wak.Screening
open AddMonoidAlgebra VirasoroScreening
open scoped BigOperators
noncomputable section

/-- A single auxiliary variable, with constant oscillator coefficient one. -/
def auxiliaryVariable (r : ℕ) (i : Fin r) : Auxiliary r := single (unitExponent r i) 1

/-- The beta factor is its literal finite polynomial in the auxiliary variable. -/
theorem betaFactor_as_powers (r D : ℕ) (i : Fin r) :
    betaFactor r D i = ∑ j∈Finset.range (D+1),
      single 0 (MvPolynomial.X (0,j) : WakFock) * auxiliaryVariable r i ^ j := by
  classical
  apply Finset.sum_congr rfl
  intro j hj
  simp [auxiliaryVariable,AddMonoidAlgebra.single_pow,
    AddMonoidAlgebra.single_mul_single,nsmul_eq_mul,zsmul_eq_mul]

/-- The finite polynomial representing (z_i B_i-z_j B_j)/(z_i-z_j).
The definition uses a geometric sum, not division. -/
def betaDivided (r D : ℕ) (i j : Fin r) : Auxiliary r :=
  ∑ d∈Finset.range (D+1), single 0 (MvPolynomial.X (0,d) : WakFock) *
    ∑ a∈Finset.range (d+1), auxiliaryVariable r i ^ a * auxiliaryVariable r j ^ (d-a)

/-- Multiplying the finite beta divided difference by z_i-z_j gives the
exact difference z_i B_i-z_j B_j, with no distinctness hypothesis. -/
theorem betaDivided_mul (r D : ℕ) (i j : Fin r) :
    betaDivided r D i j * (auxiliaryVariable r i-auxiliaryVariable r j) =
      auxiliaryVariable r i * betaFactor r D i - auxiliaryVariable r j * betaFactor r D j := by
  classical
  rw [betaDivided,betaFactor_as_powers,betaFactor_as_powers,
    Finset.sum_mul,Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [mul_assoc]
  have h := geom_sum₂_mul (auxiliaryVariable r i) (auxiliaryVariable r j) (d+1)
  simp only [Nat.add_sub_cancel] at h
  rw [h,pow_succ,pow_succ]
  ring

/-- The companion divided difference from the Vandermonde derivative is
B_i+B_j minus the beta divided difference. This again is a polynomial. -/
def betaCompanion (r D : ℕ) (i j : Fin r) : Auxiliary r :=
  betaFactor r D i+betaFactor r D j-betaDivided r D i j

/-- The companion has numerator z_i B_j-z_j B_i. This fixes the signs
needed when combining the two lowering-mode contributions. -/
theorem betaCompanion_mul (r D : ℕ) (i j : Fin r) :
    betaCompanion r D i j * (auxiliaryVariable r i-auxiliaryVariable r j) =
      auxiliaryVariable r i * betaFactor r D j - auxiliaryVariable r j * betaFactor r D i := by
  rw [betaCompanion,sub_mul,betaDivided_mul]
  ring

/-- The two actual finite divided differences add to B_i+B_j, so their
pair contribution has no denominator or residual coincidence condition. -/
theorem betaDivided_add_companion (r D : ℕ) (i j : Fin r) :
    betaDivided r D i j+betaCompanion r D i j=betaFactor r D i+betaFactor r D j := by
  rw [betaCompanion]
  ring

end
end VOA.Wak.Screening
