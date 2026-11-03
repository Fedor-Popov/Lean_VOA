import VOA.DeligneAudit.D4CharDownRegroup

/-! The common constant-term factor Gamma is a genuine invertible formal series. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open PowerSeries

noncomputable section

variable {R : Type*} [CommRing R]

/-- A diagonal bivariate series, with coefficient c(k) at bidegree (k,k). -/
def gtDiagonalSeries (c : ℕ → R) : GTBiSeries R :=
  PowerSeries.mk fun m => PowerSeries.mk fun n => if n = m then c m else 0

@[simp] theorem gtBiCoeff_diagonal (c : ℕ → R) (n m : ℕ) :
    gtBiCoeff n m (gtDiagonalSeries c) = if n = m then c m else 0 := by
  simp [gtBiCoeff, gtDiagonalSeries]

/-- Diagonal series act by the finite common-gain convolution. -/
theorem gtBiCoeff_diagonal_mul (c : ℕ → R) (F : GTBiSeries R) (n m : ℕ) :
    gtBiCoeff n m (gtDiagonalSeries c * F) =
      ∑ k ∈ Finset.range (min n m + 1), c k * gtBiCoeff (n - k) (m - k) F := by
  classical
  simp only [gtBiCoeff, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe]
  rw [coeff_mul, map_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    gtDiagonalSeries, coeff_mk, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_range]
  rw [← Finset.sum_subset (Finset.range_mono
    (show min n m + 1 ≤ m + 1 by omega))]
  · apply Finset.sum_congr rfl
    intro k hk
    have hk := Finset.mem_range.mp hk
    rw [if_pos (by omega)]
  · intro k hk hn
    have hk := Finset.mem_range.mp hk
    have hn : ¬ k < min n m + 1 := by simpa using hn
    rw [if_neg (by omega)]

theorem gtDiagonalSeries_isUnit (c : ℕ → R) (hc : c 0 = 1) :
    IsUnit (gtDiagonalSeries c) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  simp [gtDiagonalSeries, hc]

/-- The Gamma of the paper, with each alphabet given its own formal degree. -/
def gtMixedGamma (q : R) (h : PochhammerUnits q) (x y : ℕ → Rˣ) : GTBiSeries R :=
  gtDiagonalSeries fun k => gtOneRowCoeff q h x 2 k * gtOneRowCoeff q h y 2 k

theorem gtOneRowCoeff_zero_degree (q : R) (h : PochhammerUnits q) (x : ℕ → Rˣ)
    (N : ℕ) : gtOneRowCoeff q h x N 0 = 1 := by
  rw [← gtEulerInv_product_coeff, coeff_zero_eq_constantCoeff]
  simp

theorem gtMixedGamma_isUnit (q : R) (h : PochhammerUnits q) (x y : ℕ → Rˣ) :
    IsUnit (gtMixedGamma q h x y) := by
  apply gtDiagonalSeries_isUnit
  simp [gtOneRowCoeff_zero_degree]

/-- Cancellation is valid over every coefficient ring, without a domain assumption. -/
theorem gtMixedGamma_cancel (q : R) (h : PochhammerUnits q) (x y : ℕ → Rˣ)
    (F G : GTBiSeries R) (hh : gtMixedGamma q h x y * F = gtMixedGamma q h x y * G) :
    F = G := (gtMixedGamma_isUnit q h x y).mul_left_cancel hh

/-- Coefficientwise cancellation, in precisely the common-gain convolution form. -/
theorem gtMixedGamma_convolution_cancel (q : R) (h : PochhammerUnits q)
    (x y : ℕ → Rˣ) (F G : ℕ → ℕ → R)
    (hh : ∀ n m,
      (∑ k ∈ Finset.range (min n m + 1),
        (gtOneRowCoeff q h x 2 k * gtOneRowCoeff q h y 2 k) * F (n - k) (m - k)) =
      ∑ k ∈ Finset.range (min n m + 1),
        (gtOneRowCoeff q h x 2 k * gtOneRowCoeff q h y 2 k) * G (n - k) (m - k)) :
    F = G := by
  let A : GTBiSeries R := PowerSeries.mk fun m => PowerSeries.mk fun n => F n m
  let B : GTBiSeries R := PowerSeries.mk fun m => PowerSeries.mk fun n => G n m
  have he : gtMixedGamma q h x y * A = gtMixedGamma q h x y * B := by
    ext m n
    change gtBiCoeff n m (gtMixedGamma q h x y * A) =
      gtBiCoeff n m (gtMixedGamma q h x y * B)
    simp only [gtMixedGamma, gtBiCoeff_diagonal_mul]
    simpa [A, B, gtBiCoeff] using hh n m
  have he := gtMixedGamma_cancel q h x y A B he
  funext n m
  simpa [A, B, gtBiCoeff] using congrArg (gtBiCoeff (R := R) n m) he

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtBiCoeff_diagonal_mul
#print axioms VOA.DeligneAudit.D4Char.gtDiagonalSeries_isUnit
#print axioms VOA.DeligneAudit.D4Char.gtOneRowCoeff_zero_degree
#print axioms VOA.DeligneAudit.D4Char.gtMixedGamma_isUnit
#print axioms VOA.DeligneAudit.D4Char.gtMixedGamma_cancel
#print axioms VOA.DeligneAudit.D4Char.gtMixedGamma_convolution_cancel
