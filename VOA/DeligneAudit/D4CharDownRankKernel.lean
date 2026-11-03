import VOA.DeligneAudit.D4CharDownFourSeries

/-! Splitting the actual mixed Euler kernel into its rank-four and last-coordinate factors. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open PowerSeries

noncomputable section

variable {R : Type*} [CommRing R]

theorem gtEulerInv_map {S : Type*} [CommRing S] (φ : R →+* S)
    (q : R) (h : PochhammerUnits q) (a : R) :
    (gtEulerInv q h a).map φ =
      gtEulerInv (φ q) (gtPochhammerUnits_map φ q h) (φ a) := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_map, gtEulerInv, coeff_mk, map_mul, map_pow]
  rw [gtInvPoch_map]

/-- The same univariate series in two independent variables. -/
def gtSeparatePair (A : PowerSeries R) : GTBiSeries R :=
  PowerSeries.C A * A.map PowerSeries.C

theorem gtSeparatePair_mul (A B : PowerSeries R) :
    gtSeparatePair (A * B) = gtSeparatePair A * gtSeparatePair B := by
  simp only [gtSeparatePair, map_mul]
  ring

theorem gtSeparatePair_map {S : Type*} [CommRing S] (φ : R →+* S)
    (A : PowerSeries R) :
    (gtSeparatePair A).map (PowerSeries.map φ) = gtSeparatePair (A.map φ) := by
  simp only [gtSeparatePair, map_mul, PowerSeries.map_C]
  congr 1
  apply PowerSeries.ext
  intro n
  simp only [coeff_map, PowerSeries.map_C]

/-- The negative-only factor at arbitrary ambient rank. -/
def gtRankYBase (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) (N : ℕ) :
    GTBiSeries R :=
  gtSeparatePair (∏ i ∈ Finset.range N, gtEulerInv q h ((u i)⁻¹ : Rˣ))

/-- One positive formal variable of the mixed Euler kernel at rank N. -/
def gtRankXStep (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) (N : ℕ) :
    PowerSeries (GTBiSeries R) :=
  gtMixedEulerStep (R := GTBiSeries R) (gtBiC (R := R) q)
    (gtPochhammerUnits_map (S := GTBiSeries R) gtBiC q h)
    (fun i => gtBiC (R := R) (u i : R)) gtBiY N 2

/-- The same mixed Euler product as the established rank-five kernel, at rank N. -/
def gtMixedRankKernel (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) (N : ℕ) :
    GTFourSeries R :=
  gtBiC (gtRankYBase q h u N) * gtSeparatePair (gtRankXStep q h u N)

theorem gtMixedRankKernel_five (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) :
    gtMixedRankKernel q h u 5 = gtMixedFiveKernel q h u := by
  unfold gtMixedRankKernel gtMixedFiveKernel
  change gtBiC (gtMixedFiveYBase q h u) * gtSeparatePair (gtMixedFiveStep q h u) = _
  simp only [gtBiC, RingHom.comp_apply, gtSeparatePair, map_mul]
  ring

theorem gtRankYBase_succ (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) (N : ℕ) :
    gtRankYBase q h u (N + 1) = gtRankYBase q h u N *
      gtSeparatePair (gtEulerInv q h ((u N)⁻¹ : Rˣ)) := by
  rw [gtRankYBase, Finset.prod_range_succ, gtSeparatePair_mul]
  rfl

theorem gtRankXStep_succ (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) (N : ℕ) :
    gtRankXStep q h u (N + 1) = gtRankXStep q h u N *
      (gtEulerInv q h (u N : R)).map gtBiC := by
  rw [gtEulerInv_map]
  unfold gtRankXStep gtMixedEulerStep
  rw [Finset.prod_range_succ (n := N)]
  ring

/-- Exact kernel factorization; there is no restriction on any formal-variable degree. -/
theorem gtMixedRankKernel_succ (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (N : ℕ) :
    gtMixedRankKernel q h u (N + 1) = gtMixedRankKernel q h u N *
      gtBiC (gtSeparatePair (gtEulerInv q h ((u N)⁻¹ : Rˣ))) *
        gtSeparatePair ((gtEulerInv q h (u N : R)).map gtBiC) := by
  rw [gtMixedRankKernel, gtRankYBase_succ, gtRankXStep_succ, map_mul,
    gtSeparatePair_mul]
  unfold gtMixedRankKernel
  ring

theorem gtBiCollapse_gtBiC (a b r : R) :
    gtBiCollapseHom a b (gtBiC r) = PowerSeries.C r := by
  rw [gtBiC, RingHom.comp_apply, gtBiCollapse_C]
  apply PowerSeries.ext
  intro n
  by_cases hn : n = 0 <;> simp [coeff_rescale, coeff_C, hn]

theorem gtFourCollapse_gtBiC (x y : ℕ → R) (F : GTBiSeries R) :
    gtFourCollapse x y (gtBiC F) =
      PowerSeries.C (gtBiCollapseHom (y 0) (y 1) F) := by
  simp only [gtFourCollapse, gtBiC, RingHom.comp_apply, PowerSeries.map_C]
  exact gtBiCollapse_gtBiC _ _ _

theorem gtFourCollapse_separate (x y : ℕ → R) (A : PowerSeries R) :
    gtFourCollapse x y (gtSeparatePair (A.map gtBiC)) =
      (rescale (x 0) A * rescale (x 1) A).map PowerSeries.C := by
  unfold gtFourCollapse
  simp only [RingHom.comp_apply, gtSeparatePair_map]
  have hm : (A.map gtBiC).map (gtBiCollapseHom (y 0) (y 1)) =
      A.map PowerSeries.C := by
    apply PowerSeries.ext
    intro n
    simp only [coeff_map, gtBiCollapse_gtBiC]
  rw [hm, gtSeparatePair, map_mul, gtBiCollapse_C, gtBiCollapse_map_C,
    rescale_map, rescale_map, ← map_mul]

/-- Homogeneous kernel factorization, ready for last-variable specialization or CT. -/
theorem gtMixedRankKernel_collapsed_succ (q : R) (h : PochhammerUnits q)
    (x y : ℕ → R) (u : ℕ → Rˣ) (N : ℕ) :
    gtFourCollapse x y (gtMixedRankKernel q h u (N + 1)) =
      gtFourCollapse x y (gtMixedRankKernel q h u N) *
        PowerSeries.C (rescale (y 0) (gtEulerInv q h ((u N)⁻¹ : Rˣ)) *
          rescale (y 1) (gtEulerInv q h ((u N)⁻¹ : Rˣ))) *
        (rescale (x 0) (gtEulerInv q h (u N : R)) *
          rescale (x 1) (gtEulerInv q h (u N : R))).map PowerSeries.C := by
  rw [gtMixedRankKernel_succ, map_mul, map_mul, gtFourCollapse_gtBiC,
    gtFourCollapse_separate, gtSeparatePair, map_mul, gtBiCollapse_C,
    gtBiCollapse_map_C]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtEulerInv_map
#print axioms VOA.DeligneAudit.D4Char.gtSeparatePair_mul
#print axioms VOA.DeligneAudit.D4Char.gtSeparatePair_map
#print axioms VOA.DeligneAudit.D4Char.gtMixedRankKernel_five
#print axioms VOA.DeligneAudit.D4Char.gtRankYBase_succ
#print axioms VOA.DeligneAudit.D4Char.gtRankXStep_succ
#print axioms VOA.DeligneAudit.D4Char.gtMixedRankKernel_succ
#print axioms VOA.DeligneAudit.D4Char.gtBiCollapse_gtBiC
#print axioms VOA.DeligneAudit.D4Char.gtFourCollapse_gtBiC
#print axioms VOA.DeligneAudit.D4Char.gtFourCollapse_separate
#print axioms VOA.DeligneAudit.D4Char.gtMixedRankKernel_collapsed_succ
