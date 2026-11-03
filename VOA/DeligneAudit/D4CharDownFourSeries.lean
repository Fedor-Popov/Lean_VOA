import VOA.DeligneAudit.D4CharDownCollapse

/-! The proved four-degree MC kernel under homogeneous substitution in both alphabets. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open PowerSeries

noncomputable section

variable {R : Type*} [CommRing R]

theorem gtBiCollapseHom_coeff (a b : R) (F : GTBiSeries R) (n : ℕ) :
    coeff n (gtBiCollapseHom a b F) =
      ∑ r ∈ Finset.range (n + 1), a ^ r * b ^ (n - r) * gtBiCoeff r (n - r) F := by
  change coeff n (gtBiCollapse a b F) = _
  rw [gtBiCollapse, coeff_mk, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- Four independent formal variables, in the established order x_2,x_1,y_2,y_1. -/
abbrev GTFourSeries (R : Type*) := PowerSeries (PowerSeries (GTBiSeries R))

/-- Substitute x_i -> s*x_i and y_i -> t*y_i. The outer degree is now s. -/
def gtFourCollapse (x y : ℕ → R) : GTFourSeries R →+* GTBiSeries R :=
  (gtBiCollapseHom (PowerSeries.C (x 0)) (PowerSeries.C (x 1))).comp
    (PowerSeries.map (PowerSeries.map (gtBiCollapseHom (y 0) (y 1))))

/-- This is the finite homogeneous coefficient formula for the actual ring substitution. -/
theorem gtFourCollapse_coeff (x y : ℕ → R) (F : GTFourSeries R) (n m : ℕ) :
    gtBiCoeff m n (gtFourCollapse x y F) =
      ∑ r ∈ Finset.range (n + 1), ∑ t ∈ Finset.range (m + 1),
        (x 0 ^ r * x 1 ^ (n - r) * (y 0 ^ t * y 1 ^ (m - t))) *
          gtBiCoeff t (m - t) (coeff r (coeff (n - r) F)) := by
  change coeff m (coeff n
    (gtBiCollapseHom (PowerSeries.C (x 0)) (PowerSeries.C (x 1))
      (F.map (PowerSeries.map (gtBiCollapseHom (y 0) (y 1)))))) = _
  rw [gtBiCollapseHom_coeff, map_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [gtBiCoeff_map]
  rw [← map_pow, ← map_pow, ← map_mul, coeff_C_mul, gtBiCollapseHom_coeff,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact (mul_assoc _ _ _).symm

/-- Stable MC in the homogeneous series used for the down-step; no identity is assumed. -/
theorem gtMixed_five_collapsed (q : R) (h : PochhammerUnits q)
    (x y u : ℕ → Rˣ) (n m : ℕ) :
    gtBiCoeff m n
      (gtFourCollapse (fun i => (x i : R)) (fun i => (y i : R))
        (gtMixedFiveKernel q h u)) =
      ∑ p ∈ gtPartitionsTwo n, ∑ z ∈ gtPartitionsTwo m,
        gtQ q h x 2 ![(p.1 : ℤ), (p.2 : ℤ)] *
          gtQ q h y 2 ![(z.1 : ℤ), (z.2 : ℤ)] *
            gtEval q u 5 (gtMixedFiveRow p.1 p.2 z.1 z.2) := by
  rw [gtFourCollapse_coeff]
  simp_rw [gtMixedFiveKernel_coeff]
  exact (gtMixed_five_homogeneous q h x y u n m).symm

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtBiCollapseHom_coeff
#print axioms VOA.DeligneAudit.D4Char.gtFourCollapse_coeff
#print axioms VOA.DeligneAudit.D4Char.gtMixed_five_collapsed
