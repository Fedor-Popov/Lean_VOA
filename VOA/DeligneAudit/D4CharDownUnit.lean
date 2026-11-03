import VOA.DeligneAudit.D4CharDownRankKernel

/-! Full branching at w = 1: an equivalent down-step using a separable Euler unit. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open PowerSeries

noncomputable section

variable {R : Type*} [CommRing R]

def gtOneRowSeries (q : R) (h : PochhammerUnits q) (x : ℕ → Rˣ) : PowerSeries R :=
  ∏ i ∈ Finset.range 2, gtEulerInv q h (x i : R)

/-- The four removed Euler factors at w = 1, with x-degree outermost. -/
def gtMixedExtra (q : R) (h : PochhammerUnits q) (x y : ℕ → Rˣ) : GTBiSeries R :=
  PowerSeries.C (gtOneRowSeries q h y) * (gtOneRowSeries q h x).map PowerSeries.C

theorem gtMixedExtra_coeff (q : R) (h : PochhammerUnits q) (x y : ℕ → Rˣ)
    (n m : ℕ) :
    gtBiCoeff m n (gtMixedExtra q h x y) =
      gtOneRowCoeff q h x 2 n * gtOneRowCoeff q h y 2 m := by
  simp only [gtMixedExtra, gtBiCoeff, AddMonoidHom.comp_apply,
    LinearMap.toAddMonoidHom_coe, coeff_C_mul, coeff_map, coeff_mul_C, gtOneRowSeries]
  rw [gtEulerInv_product_coeff, gtEulerInv_product_coeff, mul_comm]

theorem gtMixedExtra_isUnit (q : R) (h : PochhammerUnits q) (x y : ℕ → Rˣ) :
    IsUnit (gtMixedExtra q h x y) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  have hc : constantCoeff (constantCoeff (gtMixedExtra q h x y)) = 1 := by
    simpa only [gtBiCoeff, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
      coeff_zero_eq_constantCoeff, gtOneRowCoeff_zero_degree, one_mul] using
        gtMixedExtra_coeff q h x y 0 0
  rw [hc]
  exact isUnit_one

theorem gtMixedExtra_mul_coeff (q : R) (h : PochhammerUnits q) (x y : ℕ → Rˣ)
    (F : GTBiSeries R) (n m : ℕ) :
    gtBiCoeff m n (gtMixedExtra q h x y * F) =
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        (gtOneRowCoeff q h x 2 k * gtOneRowCoeff q h y 2 l) *
          gtBiCoeff (m - l) (n - k) F := by
  rw [gtBiCoeff_mul]
  simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, gtMixedExtra_coeff]

/-- The complete GL_4 mixed sum, with separate homogeneous degrees for x and y. -/
def gtMixedFourSeries (q : R) (h : PochhammerUnits q) (x y u : ℕ → Rˣ) :
    GTBiSeries R :=
  PowerSeries.mk fun n => PowerSeries.mk fun m =>
    ∑ p ∈ gtPartitionsTwo n, ∑ z ∈ gtPartitionsTwo m,
      gtQ q h x 2 ![(p.1 : ℤ), (p.2 : ℤ)] *
        gtQ q h y 2 ![(z.1 : ℤ), (z.2 : ℤ)] *
          gtEval q u 4 (gtMixedFourRow p.1 p.2 z.1 z.2)

def gtMixedFiveSeries (q : R) (h : PochhammerUnits q) (x y u : ℕ → Rˣ) :
    GTBiSeries R :=
  PowerSeries.mk fun n => PowerSeries.mk fun m =>
    ∑ p ∈ gtPartitionsTwo n, ∑ z ∈ gtPartitionsTwo m,
      gtQ q h x 2 ![(p.1 : ℤ), (p.2 : ℤ)] *
        gtQ q h y 2 ![(z.1 : ℤ), (z.2 : ℤ)] *
          gtEval q u 5 (gtMixedFiveRow p.1 p.2 z.1 z.2)

/-- The full gP regrouping at w = 1 retains both gains independently. -/
theorem gtMixedFive_hom_branch_one (q : R) (h : PochhammerUnits q)
    (x y u : ℕ → Rˣ) (hu : u 4 = 1) (n m : ℕ) :
    (∑ p ∈ gtPartitionsTwo n, ∑ z ∈ gtPartitionsTwo m,
      gtQ q h x 2 ![(p.1 : ℤ), (p.2 : ℤ)] *
        gtQ q h y 2 ![(z.1 : ℤ), (z.2 : ℤ)] *
          gtEval q u 5 (gtMixedFiveRow p.1 p.2 z.1 z.2)) =
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        (gtOneRowCoeff q h x 2 k * gtOneRowCoeff q h y 2 l) *
          ∑ c ∈ gtPartitionsTwo (n - k), ∑ d ∈ gtPartitionsTwo (m - l),
            gtQ q h x 2 ![(c.1 : ℤ), (c.2 : ℤ)] *
              gtQ q h y 2 ![(d.1 : ℤ), (d.2 : ℤ)] *
                gtEval q u 4 (gtMixedFourRow c.1 c.2 d.1 d.2) := by
  rw [← gtDownTwo_transform_pair]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  rw [gtMixedFive_branching]
  simp_rw [sum_gtRows_three_nat]
  simp [hu]

/-- The GT generating series loses exactly the four last-coordinate Euler factors. -/
theorem gtMixedFiveSeries_branch_one (q : R) (h : PochhammerUnits q)
    (x y u : ℕ → Rˣ) (hu : u 4 = 1) :
    gtMixedFiveSeries q h x y u = gtMixedExtra q h x y * gtMixedFourSeries q h x y u := by
  apply PowerSeries.ext
  intro n
  apply PowerSeries.ext
  intro m
  change gtBiCoeff m n (gtMixedFiveSeries q h x y u) =
    gtBiCoeff m n (gtMixedExtra q h x y * gtMixedFourSeries q h x y u)
  rw [gtMixedExtra_mul_coeff]
  simpa only [gtBiCoeff, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    gtMixedFiveSeries, gtMixedFourSeries, coeff_mk] using
      gtMixedFive_hom_branch_one q h x y u hu n m

theorem gtMixedFiveSeries_eq_kernel (q : R) (h : PochhammerUnits q)
    (x y u : ℕ → Rˣ) :
    gtMixedFiveSeries q h x y u =
      gtFourCollapse (fun i => (x i : R)) (fun i => (y i : R))
        (gtMixedFiveKernel q h u) := by
  apply PowerSeries.ext
  intro n
  apply PowerSeries.ext
  intro m
  simpa only [gtMixedFiveSeries, coeff_mk] using
    (gtMixed_five_collapsed q h x y u n m).symm

theorem gtEulerInv_rescale_one (q : R) (h : PochhammerUnits q) (a : R) :
    rescale a (gtEulerInv q h 1) = gtEulerInv q h a := by
  apply PowerSeries.ext
  intro n
  simp [coeff_rescale, gtEulerInv, mul_comm]

/-- The actual Euler kernel has the same removable unit as the full GT branching sum. -/
theorem gtMixedFiveKernel_branch_one (q : R) (h : PochhammerUnits q)
    (x y u : ℕ → Rˣ) (hu : u 4 = 1) :
    gtFourCollapse (fun i => (x i : R)) (fun i => (y i : R))
        (gtMixedFiveKernel q h u) =
      gtMixedExtra q h x y *
        gtFourCollapse (fun i => (x i : R)) (fun i => (y i : R))
          (gtMixedRankKernel q h u 4) := by
  rw [← gtMixedRankKernel_five, show 5 = 4 + 1 from rfl,
    gtMixedRankKernel_collapsed_succ]
  simp only [hu, inv_one, Units.val_one, gtEulerInv_rescale_one]
  have hp (z : ℕ → Rˣ) : gtOneRowSeries q h z =
      gtEulerInv q h (z 0 : R) * gtEulerInv q h (z 1 : R) := by
    simp [gtOneRowSeries, Finset.prod_range_succ]
  rw [← hp y, ← hp x]
  unfold gtMixedExtra
  ring

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtMixedExtra_coeff
#print axioms VOA.DeligneAudit.D4Char.gtMixedExtra_isUnit
#print axioms VOA.DeligneAudit.D4Char.gtMixedExtra_mul_coeff
#print axioms VOA.DeligneAudit.D4Char.gtMixedFive_hom_branch_one
#print axioms VOA.DeligneAudit.D4Char.gtMixedFiveSeries_branch_one
#print axioms VOA.DeligneAudit.D4Char.gtMixedFiveSeries_eq_kernel
#print axioms VOA.DeligneAudit.D4Char.gtEulerInv_rescale_one
#print axioms VOA.DeligneAudit.D4Char.gtMixedFiveKernel_branch_one
