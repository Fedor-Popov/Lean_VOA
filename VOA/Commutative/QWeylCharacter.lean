import VOA.Commutative.QJacobiCube
import Mathlib.RingTheory.PowerSeries.Expand

/-! # Finite coefficient formula for the affine Weyl alternating character

The signed parabolic terms have coefficient `(2*r+1)` and energy shift
`p * choose(r+1,2)`. This file proves their formal product, independently of
whether an actual representation has an exact parabolic resolution.
-/

namespace VOA.QSeries
open scoped BigOperators
noncomputable section

variable {K : Type*} [Field K]

/-- Expansion preserves finite coefficient cutoffs for the triangular sum. -/
theorem coeff_expand_alternatingTheta_mul
    (p : ℕ) (hp : p ≠ 0) (B : PowerSeries K) (n N : ℕ) (h : n ≤ N) :
    PowerSeries.coeff n (PowerSeries.expand p hp alternatingTheta * B) =
      ∑ r ∈ Finset.range (N+1),
        PowerSeries.coeff n (PowerSeries.expand p hp (alternatingTerm r) * B) := by
  have heq : PowerSeries.coeff n (PowerSeries.expand p hp alternatingTheta * B) =
      PowerSeries.coeff n
        (PowerSeries.expand p hp (∑ r ∈ Finset.range (N+1), alternatingTerm r) * B) := by
    apply coeff_mul_congr_left_upto
    intro i hi
    rw [PowerSeries.coeff_expand, PowerSeries.coeff_expand]
    split_ifs
    · exact coeff_alternatingTheta (i / p) N ((Nat.div_le_self i p).trans (hi.trans h))
    · rfl
  rw [heq]
  simp only [map_sum, Finset.sum_mul]

/-- The actual finite alternating Weyl coefficient equals the Euler product. -/
theorem coeff_weyl_alternating_eq_product (p : ℕ) (hp : p ≠ 0) (n : ℕ) :
    (∑ r ∈ Finset.range (n+1),
      PowerSeries.coeff n
        (PowerSeries.expand p hp (alternatingTerm r : PowerSeries K) * reciprocalEuler^3)) =
      PowerSeries.coeff n
        ((PowerSeries.expand p hp (euler : PowerSeries K))^3 * reciprocalEuler^3) := by
  rw [← coeff_expand_alternatingTheta_mul p hp _ n n le_rfl, jacobi_cube, map_pow]

/-- The unsigned shifted vacuum coefficient of the horizontal spin-r term. -/
def weylTermCoefficient (p n r : ℕ) : K :=
  if p * (r+1).choose 2 ≤ n then
    (2*r+1 : ℕ) * PowerSeries.coeff (n-p*(r+1).choose 2) (reciprocalEuler^3 : PowerSeries K)
  else 0

/-- Expansion makes the actual triangular energy shift explicit. -/
theorem coeff_expanded_alternatingTerm (p : ℕ) (hp : p ≠ 0) (n r : ℕ) :
    PowerSeries.coeff n
      (PowerSeries.expand p hp (alternatingTerm r : PowerSeries K) * reciprocalEuler^3) =
      (-1 : K)^r * weylTermCoefficient p n r := by
  have hc : (-1 : PowerSeries K)^r * ((2*r+1 : ℕ) : PowerSeries K) =
      PowerSeries.C ((-1 : K)^r * ((2*r+1 : ℕ) : K)) := by
    simp only [map_mul,map_pow,map_neg,map_one,map_natCast]
  have he : PowerSeries.expand p hp (alternatingTerm r : PowerSeries K) =
      PowerSeries.C ((-1 : K)^r * ((2*r+1 : ℕ) : K)) *
        PowerSeries.X^(p*(r+1).choose 2) := by
    simp only [alternatingTerm,map_mul,map_pow,map_neg,map_one,map_natCast,
      PowerSeries.expand_X,← pow_mul]
  rw [he,mul_assoc,PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow_mul']
  unfold weylTermCoefficient
  split_ifs <;> ring

/-- The product coefficient is the explicit finite alternating sum of shifted
vacuum coefficients. -/
theorem coeff_weyl_product_eq_sum (p : ℕ) (hp : p ≠ 0) (n : ℕ) :
    PowerSeries.coeff n
      ((PowerSeries.expand p hp (euler : PowerSeries K))^3 * reciprocalEuler^3) =
      ∑ r ∈ Finset.range (n+1), (-1 : K)^r * weylTermCoefficient p n r := by
  rw [← coeff_weyl_alternating_eq_product]
  apply Finset.sum_congr rfl
  intro r hr
  exact coeff_expanded_alternatingTerm p hp n r

end
end VOA.QSeries
