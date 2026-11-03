import VOA.DeligneAudit.D4CharMixedFiveDominant

/-! The mixed Euler kernel and its q-difference uniqueness reduction. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open PowerSeries

noncomputable section

variable {R : Type*} [CommRing R]

/-- The factor introduced by a new x variable z in the mixed-Cauchy kernel. -/
def gtMixedEulerStep (q : R) (h : PochhammerUnits q) (u y : ℕ → R)
    (N n : ℕ) : PowerSeries R :=
  (∏ j ∈ Finset.range n, gtEulerPos q h (y j)) *
    ∏ i ∈ Finset.range N, gtEulerInv q h (u i)

@[simp] theorem constantCoeff_gtMixedEulerStep (q : R) (h : PochhammerUnits q)
    (u y : ℕ → R) (N n : ℕ) :
    constantCoeff (gtMixedEulerStep q h u y N n) = 1 := by
  simp [gtMixedEulerStep]

theorem gtEulerPos_product_shift (q : R) (h : PochhammerUnits q)
    (y : ℕ → R) (n : ℕ) :
    (∏ j ∈ Finset.range n, gtEulerPos q h (y j)) =
      (∏ j ∈ Finset.range n, (1 - PowerSeries.C (y j) * X)) *
        rescale q (∏ j ∈ Finset.range n, gtEulerPos q h (y j)) := by
  rw [map_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  exact gtEulerPos_shift q h (y j)

/-- The stable mixed-Cauchy kernel equation, with its y-side denominator retained. -/
theorem gtMixedEulerStep_shift (q : R) (h : PochhammerUnits q)
    (u y : ℕ → R) (N n : ℕ) :
    rescale q (gtMixedEulerStep q h u y N n) *
        (∏ j ∈ Finset.range n, (1 - PowerSeries.C (y j) * X)) =
      gtMixedEulerStep q h u y N n *
        ∏ i ∈ Finset.range N, (1 - PowerSeries.C (u i) * X) := by
  rw [gtMixedEulerStep, map_mul, gtEulerInv_product_shift]
  have hp := gtEulerPos_product_shift q h y n
  calc
    _ = ((∏ j ∈ Finset.range n, (1 - PowerSeries.C (y j) * X)) *
          rescale q (∏ j ∈ Finset.range n, gtEulerPos q h (y j))) *
        (∏ i ∈ Finset.range N, gtEulerInv q h (u i)) *
          (∏ i ∈ Finset.range N, (1 - PowerSeries.C (u i) * X)) := by ring
    _ = _ := by rw [← hp]

/-- A mixed-Cauchy step is determined by its initial value and the local shift equation. -/
theorem gtMixedEulerStep_unique (q : R) (h : PochhammerUnits q)
    (u y : ℕ → R) (N n : ℕ) (F : PowerSeries R) (c : R)
    (hzero : constantCoeff F = c)
    (hshift : rescale q F *
      (∏ j ∈ Finset.range n, (1 - PowerSeries.C (y j) * X)) =
      F * ∏ i ∈ Finset.range N, (1 - PowerSeries.C (u i) * X)) :
    F = PowerSeries.C c * gtMixedEulerStep q h u y N n := by
  apply qDifference_unique q (pochhammerUnits_qDifferenceUnits q h)
    (∏ j ∈ Finset.range n, (1 - PowerSeries.C (y j) * X))
    (∏ i ∈ Finset.range N, (1 - PowerSeries.C (u i) * X))
    F (PowerSeries.C c * gtMixedEulerStep q h u y N n) (by simp) (by simp) hshift
  · have hc : rescale q (PowerSeries.C c) = PowerSeries.C c := by
      ext k
      by_cases hk : k = 0 <;> simp [coeff_rescale, coeff_C, hk]
    rw [map_mul, hc, mul_assoc, gtMixedEulerStep_shift]
    ring
  · simpa using hzero

/-- Coefficient form of the same uniqueness step, convenient for finite GT expansions. -/
theorem gtMixedEulerStep_coeff_of_shift (q : R) (h : PochhammerUnits q)
    (u y : ℕ → R) (N n : ℕ) (F : PowerSeries R) (c : R)
    (hzero : constantCoeff F = c)
    (hshift : rescale q F *
      (∏ j ∈ Finset.range n, (1 - PowerSeries.C (y j) * X)) =
      F * ∏ i ∈ Finset.range N, (1 - PowerSeries.C (u i) * X)) (k : ℕ) :
    coeff k F = c * coeff k (gtMixedEulerStep q h u y N n) := by
  rw [gtMixedEulerStep_unique q h u y N n F c hzero hshift, coeff_C_mul]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.constantCoeff_gtMixedEulerStep
#print axioms VOA.DeligneAudit.D4Char.gtEulerPos_product_shift
#print axioms VOA.DeligneAudit.D4Char.gtMixedEulerStep_shift
#print axioms VOA.DeligneAudit.D4Char.gtMixedEulerStep_unique
#print axioms VOA.DeligneAudit.D4Char.gtMixedEulerStep_coeff_of_shift
