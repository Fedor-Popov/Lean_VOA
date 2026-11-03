import VOA.DeligneAudit.D4CharDownEuler

/-! The last-coordinate Euler constant term, including multiplication by the lower kernel. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open PowerSeries

noncomputable section

variable {R : Type*} [CommRing R]

/-- The four inverse Euler factors contributed by the removed GL coordinate w. -/
def gtLastEulerPair (q : R) (h : PochhammerUnits q) (x y : ℕ → Rˣ) :
    GTBiSeries (GTLastLaurent R) :=
  let A := ∏ i ∈ Finset.range 2,
    gtEulerInv (gtLastC q) (gtPochhammerUnits_map gtLastC q h)
      (AddMonoidAlgebra.single 1 (x i : R))
  let B := ∏ i ∈ Finset.range 2,
    gtEulerInv (gtLastC q) (gtPochhammerUnits_map gtLastC q h)
      (AddMonoidAlgebra.single (-1) (y i : R))
  PowerSeries.C A * B.map PowerSeries.C

/-- Every last-coordinate monomial is retained before extracting its constant term. -/
theorem gtLastEulerPair_coeff (q : R) (h : PochhammerUnits q) (x y : ℕ → Rˣ)
    (n m : ℕ) :
    gtBiCoeff n m (gtLastEulerPair q h x y) =
      AddMonoidAlgebra.single ((n : ℤ) - m)
        (gtOneRowCoeff q h x 2 n * gtOneRowCoeff q h y 2 m) := by
  simp only [gtLastEulerPair, gtBiCoeff, AddMonoidHom.comp_apply,
    LinearMap.toAddMonoidHom_coe, coeff_C_mul, coeff_map, coeff_mul_C]
  rw [gtLastEuler_product_coeff q h x 1, gtLastEuler_product_coeff q h y (-1),
    AddMonoidAlgebra.single_mul_single]
  simp [sub_eq_add_neg]

/-- Take the w constant term separately in every formal bidegree. -/
def gtLastCTBi (F : GTBiSeries (GTLastLaurent R)) : GTBiSeries R :=
  PowerSeries.mk fun m => PowerSeries.mk fun n => (gtBiCoeff n m F) 0

@[simp] theorem gtLastCTBi_coeff (F : GTBiSeries (GTLastLaurent R)) (n m : ℕ) :
    gtBiCoeff n m (gtLastCTBi F) = (gtBiCoeff n m F) 0 := by
  simp [gtLastCTBi, gtBiCoeff]

/-- The constant term of the actual last-coordinate Euler factors is Gamma. -/
theorem gtLastEulerPair_ct (q : R) (h : PochhammerUnits q) (x y : ℕ → Rˣ) :
    gtLastCTBi (gtLastEulerPair q h x y) = gtMixedGamma q h x y := by
  apply PowerSeries.ext
  intro m
  apply PowerSeries.ext
  intro n
  change gtBiCoeff n m (gtLastCTBi (gtLastEulerPair q h x y)) =
    gtBiCoeff n m (gtMixedGamma q h x y)
  rw [gtLastCTBi_coeff, gtLastEulerPair_coeff, gtMixedGamma, gtBiCoeff_diagonal]
  simp only [AddMonoidAlgebra.single_apply, sub_eq_zero, Nat.cast_inj]
  by_cases hn : n = m <;> simp [hn]

theorem gtBiCoeff_mul (F G : GTBiSeries R) (n m : ℕ) :
    gtBiCoeff n m (F * G) = ∑ b ∈ Finset.antidiagonal m,
      ∑ a ∈ Finset.antidiagonal n,
        gtBiCoeff a.1 b.1 F * gtBiCoeff a.2 b.2 G := by
  simp [gtBiCoeff, coeff_mul, map_sum]

theorem gtBiCoeff_map {S : Type*} [CommRing S] (φ : R →+* S)
    (F : GTBiSeries R) (n m : ℕ) :
    gtBiCoeff n m (F.map (PowerSeries.map φ)) = φ (gtBiCoeff n m F) := by
  simp [gtBiCoeff, coeff_map]

/-- Taking CT after adjoining the last coordinate multiplies any lower kernel by Gamma. -/
theorem gtLastEulerPair_mul_ct (q : R) (h : PochhammerUnits q) (x y : ℕ → Rˣ)
    (F : GTBiSeries R) :
    gtLastCTBi (gtLastEulerPair q h x y * F.map (PowerSeries.map gtLastC)) =
      gtMixedGamma q h x y * F := by
  apply PowerSeries.ext
  intro m
  apply PowerSeries.ext
  intro n
  change gtBiCoeff n m
      (gtLastCTBi (gtLastEulerPair q h x y * F.map (PowerSeries.map gtLastC))) =
    gtBiCoeff n m (gtMixedGamma q h x y * F)
  rw [gtLastCTBi_coeff, gtBiCoeff_mul, gtBiCoeff_mul]
  change (∑ b ∈ Finset.antidiagonal m, ∑ a ∈ Finset.antidiagonal n,
    gtBiCoeff a.1 b.1 (gtLastEulerPair q h x y) *
      gtBiCoeff a.2 b.2 (F.map (PowerSeries.map gtLastC))).coeff 0 = _
  simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  rw [gtLastEulerPair_coeff, gtBiCoeff_map, gtLastC_apply,
    AddMonoidAlgebra.single_mul_single, add_zero, gtMixedGamma, gtBiCoeff_diagonal]
  simp only [AddMonoidAlgebra.coeff, AddMonoidAlgebra.single_apply,
    sub_eq_zero, Nat.cast_inj]
  by_cases he : a.1 = b.1 <;> simp [he]

/-- Coefficient form of the kernel constant-term identity used in the down-step. -/
theorem gtLastEulerPair_mul_ct_coeff (q : R) (h : PochhammerUnits q) (x y : ℕ → Rˣ)
    (F : GTBiSeries R) (n m : ℕ) :
    (gtBiCoeff n m
      (gtLastEulerPair q h x y * F.map (PowerSeries.map gtLastC))) 0 =
      ∑ k ∈ Finset.range (min n m + 1),
        (gtOneRowCoeff q h x 2 k * gtOneRowCoeff q h y 2 k) *
          gtBiCoeff (n - k) (m - k) F := by
  rw [← gtLastCTBi_coeff, gtLastEulerPair_mul_ct, gtMixedGamma,
    gtBiCoeff_diagonal_mul]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtLastEulerPair_coeff
#print axioms VOA.DeligneAudit.D4Char.gtLastEulerPair_ct
#print axioms VOA.DeligneAudit.D4Char.gtBiCoeff_mul
#print axioms VOA.DeligneAudit.D4Char.gtBiCoeff_map
#print axioms VOA.DeligneAudit.D4Char.gtLastEulerPair_mul_ct
#print axioms VOA.DeligneAudit.D4Char.gtLastEulerPair_mul_ct_coeff
