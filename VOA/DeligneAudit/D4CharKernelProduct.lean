import VOA.DeligneAudit.D4CharKernelDiagonal

/-! The full homogeneous Euler product, including all four numerator factors. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open PowerSeries

noncomputable section

variable {R : Type*} [CommRing R]

theorem gtFourCollapse_separate_any (x y : ℕ → R) (A : PowerSeries (GTBiSeries R)) :
    gtFourCollapse x y (gtSeparatePair A) =
      rescale (PowerSeries.C (x 0)) (A.map (gtBiCollapseHom (y 0) (y 1))) *
        rescale (PowerSeries.C (x 1)) (A.map (gtBiCollapseHom (y 0) (y 1))) := by
  unfold gtFourCollapse
  dsimp only [RingHom.comp_apply]
  rw [gtSeparatePair_map, gtSeparatePair, map_mul, gtBiCollapse_C, gtBiCollapse_map_C]

theorem gtBiCollapse_y (y : ℕ → R) (j : Fin 2) :
    gtBiCollapseHom (y 0) (y 1) (gtBiY j) = PowerSeries.C (y j) * X := by
  fin_cases j
  · simp [gtBiY, gtBiCollapse_C, rescale_X]
  · change gtBiCollapseHom (y 0) (y 1) (X : GTBiSeries R) = _
    rw [← PowerSeries.map_X (PowerSeries.C : R →+* PowerSeries R), gtBiCollapse_map_C]
    exact rescale_X _

theorem gtEulerPos_congr_nome {q q' : R} (h : PochhammerUnits q)
    (h' : PochhammerUnits q') (he : q = q') (a : R) :
    gtEulerPos q h a = gtEulerPos q' h' a := by
  subst q'
  rfl

/-- Each of the two y variables contributes two quadratic numerator factors. -/
theorem gtFourDiagonal_numerator (q : R) (h : PochhammerUnits q)
    (x y : ℕ → R) (j : Fin 2) :
    gtBiCollapseHom 1 1 (gtFourCollapse x y
      (gtSeparatePair (gtEulerPos (R := GTBiSeries R) (gtBiC q)
        (gtPochhammerUnits_map (S := GTBiSeries R) gtBiC q h) (gtBiY j)))) =
      expand 2 two_ne_zero (gtEulerPos q h (x 0 * y j)) *
        expand 2 two_ne_zero (gtEulerPos q h (x 1 * y j)) := by
  rw [gtFourCollapse_separate_any]
  rw [gtEulerPos_map]
  simp only [gtBiCollapse_y]
  have hc := gtBiCollapse_gtBiC (y 0) (y 1) q
  rw [gtEulerPos_congr_nome _
    (gtPochhammerUnits_map (S := PowerSeries R) PowerSeries.C q h) hc]
  have hm (a b : R) : PowerSeries.C a * (PowerSeries.C b * X) =
      PowerSeries.C (a * b) * X := by rw [← mul_assoc, ← map_mul]
  simp only [gtEulerPos_rescale, hm]
  rw [map_mul, gtBiCollapse_eulerPos q h, gtBiCollapse_eulerPos q h]
  simp only [one_mul]

/-- The rank-zero kernel consists exactly of the four mixed numerator factors. -/
theorem gtFourDiagonal_zero (q : R) (h : PochhammerUnits q)
    (x y : ℕ → R) (u : ℕ → Rˣ) :
    gtBiCollapseHom 1 1 (gtFourCollapse x y (gtMixedRankKernel q h u 0)) =
      (expand 2 two_ne_zero (gtEulerPos q h (x 0 * y 0)) *
        expand 2 two_ne_zero (gtEulerPos q h (x 1 * y 0))) *
      (expand 2 two_ne_zero (gtEulerPos q h (x 0 * y 1)) *
        expand 2 two_ne_zero (gtEulerPos q h (x 1 * y 1))) := by
  have hy : gtRankYBase q h u 0 = 1 := by
    simp [gtRankYBase, gtSeparatePair]
  have hx : gtRankXStep q h u 0 =
      gtEulerPos (R := GTBiSeries R) (gtBiC q)
        (gtPochhammerUnits_map (S := GTBiSeries R) gtBiC q h) (gtBiY 0) *
      gtEulerPos (R := GTBiSeries R) (gtBiC q)
        (gtPochhammerUnits_map (S := GTBiSeries R) gtBiC q h) (gtBiY 1) := by
    simp [gtRankXStep, gtMixedEulerStep, Finset.prod_range_succ]
  rw [gtMixedRankKernel, hy, map_one, one_mul, hx, gtSeparatePair_mul,
    map_mul, map_mul]
  exact congrArg₂ (· * ·) (gtFourDiagonal_numerator q h x y 0)
    (gtFourDiagonal_numerator q h x y 1)

/-- Every extra ambient coordinate contributes its four inverse Euler factors. -/
theorem gtFourDiagonal_succ (q : R) (h : PochhammerUnits q)
    (x y : ℕ → R) (u : ℕ → Rˣ) (N : ℕ) :
    gtBiCollapseHom 1 1 (gtFourCollapse x y (gtMixedRankKernel q h u (N + 1))) =
      gtBiCollapseHom 1 1 (gtFourCollapse x y (gtMixedRankKernel q h u N)) *
        (rescale (y 0) (gtEulerInv q h ((u N)⁻¹ : Rˣ)) *
          rescale (y 1) (gtEulerInv q h ((u N)⁻¹ : Rˣ))) *
        (rescale (x 0) (gtEulerInv q h (u N : R)) *
          rescale (x 1) (gtEulerInv q h (u N : R))) := by
  rw [gtMixedRankKernel_collapsed_succ, map_mul, map_mul,
    gtBiCollapse_C, gtBiCollapse_map_C]
  simp only [rescale_one, RingHom.id_apply]

/-- The complete factorization at arbitrary ambient rank and arbitrary alphabets. -/
theorem gtFourDiagonal_product (q : R) (h : PochhammerUnits q)
    (x y : ℕ → R) (u : ℕ → Rˣ) (N : ℕ) :
    gtBiCollapseHom 1 1 (gtFourCollapse x y (gtMixedRankKernel q h u N)) =
      ((expand 2 two_ne_zero (gtEulerPos q h (x 0 * y 0)) *
        expand 2 two_ne_zero (gtEulerPos q h (x 1 * y 0))) *
      (expand 2 two_ne_zero (gtEulerPos q h (x 0 * y 1)) *
        expand 2 two_ne_zero (gtEulerPos q h (x 1 * y 1)))) *
      ∏ i ∈ Finset.range N,
        ((rescale (y 0) (gtEulerInv q h ((u i)⁻¹ : Rˣ)) *
          rescale (y 1) (gtEulerInv q h ((u i)⁻¹ : Rˣ))) *
        (rescale (x 0) (gtEulerInv q h (u i : R)) *
          rescale (x 1) (gtEulerInv q h (u i : R)))) := by
  induction N with
  | zero => simpa using gtFourDiagonal_zero q h x y u
  | succ N ih =>
      rw [gtFourDiagonal_succ, ih, Finset.prod_range_succ]
      ring

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtFourCollapse_separate_any
#print axioms VOA.DeligneAudit.D4Char.gtBiCollapse_y
#print axioms VOA.DeligneAudit.D4Char.gtFourDiagonal_numerator
#print axioms VOA.DeligneAudit.D4Char.gtFourDiagonal_zero
#print axioms VOA.DeligneAudit.D4Char.gtFourDiagonal_succ
#print axioms VOA.DeligneAudit.D4Char.gtFourDiagonal_product

#print axioms VOA.DeligneAudit.D4Char.gtEulerPos_congr_nome
