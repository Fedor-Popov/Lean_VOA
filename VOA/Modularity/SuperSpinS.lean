/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.SuperSpinAnalytic

/-!
# Proven `S` cells for the invariant spin sector

The full four-characteristic `S` law needs the characteristic-theta logarithmic-derivative
expansion isolated in `SuperSpinThetaBridge`.  The invariant `(+, +)` odd-index family admits a
shorter independent route: its formal coefficients are already exactly `zhuG`, so its analytic
evaluation is `zhuGC`.  This file performs the even-index reindexing and then
inherits the established Eisenstein `S` law.

Thus every invariant relation coefficient of weight at least four is covered, and weight two is
kept separate as the genuine `G2` anomaly.  The exceptional `k = 0` constant is deliberately not
assigned a false weight-one law.
-/

namespace VOA

open Complex
open scoped MatrixGroups

set_option autoImplicit false

private theorem spinS00 : ModularGroup.S 0 0 = 0 := by decide
private theorem spinS01 : ModularGroup.S 0 1 = -1 := by decide
private theorem spinS10 : ModularGroup.S 1 0 = 1 := by decide
private theorem spinS11 : ModularGroup.S 1 1 = 0 := by decide

/-- The half-lattice evaluation of the invariant odd family is exactly the existing analytic
Zhu--Eisenstein function. -/
theorem spinQAnalytic_pp_odd_eq_zhuGC {j : Nat} (hj : j ≠ 0) {z : Complex}
    (hz : z ∈ imGT 0) :
    spinQAnalytic SpinPair.pp (2 * j - 1) z = zhuGC j z := by
  let f : Nat → Complex := fun N => spinQAnalyticTerm SpinPair.pp (2 * j - 1) N z
  have hf : Summable f := summable_spinQAnalyticTerm SpinPair.pp (2 * j - 1) hz
  have he : Summable (fun n => f (2 * n)) :=
    hf.comp_injective (mul_right_injective₀ (by norm_num : (2 : Nat) ≠ 0))
  have ho : Summable (fun n => f (2 * n + 1)) :=
    hf.comp_injective ((add_left_injective 1).comp
      (mul_right_injective₀ (by norm_num : (2 : Nat) ≠ 0)))
  rw [spinQAnalytic, zhuGC, ← tsum_even_add_odd he ho]
  have hodd : ∀ n : Nat, f (2 * n + 1) = 0 := by
    intro n
    dsimp [f, spinQAnalyticTerm]
    change spinQ SpinPair.pp (2 * j - 1) (halfQExponent (2 * n + 1)) *
      Complex.exp (spinTwoPiI * z * halfQExponent (2 * n + 1)) = 0
    rw [spinQ_apply]
    change (spinTwoPiI ^ (2 * j - 1 + 1))⁻¹ *
        spinP ⟨SpinPhase.plus, SpinPhase.plus⟩ (2 * j - 1)
          (halfQExponent (2 * n + 1)) *
        Complex.exp (spinTwoPiI * z * halfQExponent (2 * n + 1)) = 0
    rw [spinP_plus_odd SpinPhase.plus (2 * j - 1) (2 * n + 1) ⟨n, rfl⟩]
    simp
  rw [show (∑' n : Nat, f (2 * n + 1)) = 0 by simp_rw [hodd]; exact tsum_zero,
    add_zero]
  refine tsum_congr fun n => ?_
  dsimp [f, spinQAnalyticTerm]
  change spinQ SpinPair.pp (2 * j - 1) (halfQExponent (2 * n)) *
      Complex.exp (spinTwoPiI * z * halfQExponent (2 * n)) =
    zhuG j n * Complex.exp (2 * (Real.pi : Complex) * Complex.I * (n : Complex) * z)
  have hhalf : halfQExponent (2 * n) = (n : Complex) := by
    simp [halfQExponent]
  rw [hhalf, spinQ_pp_odd_eq_zhuG hj]
  congr 1
  simp [spinTwoPiI]
  ring

/-- The invariant higher family obeys the exact normalized `S` law. -/
theorem spinQAnalytic_pp_higher_S {j : Nat} (hj : 2 ≤ j) {z : Complex}
    (hz : z ∈ imGT 0) :
    spinQAnalytic SpinPair.pp (2 * j - 1) (-1 / z) =
      z ^ (2 * j) * spinQAnalytic SpinPair.pp (2 * j - 1) z := by
  have hzS : -1 / z ∈ imGT 0 := by
    simpa [mobiusC, denomC, spinS00, spinS01, spinS10, spinS11] using
      mobiusC_mem_imGT ModularGroup.S hz
  rw [spinQAnalytic_pp_odd_eq_zhuGC (by omega) hzS,
    spinQAnalytic_pp_odd_eq_zhuGC (by omega) hz]
  have hmod : zhuGC j (-1 / z) * z ^ (-(2 * j : Int)) = zhuGC j z := by
    simpa [slashC, mobiusC, denomC, spinS00, spinS01, spinS10, spinS11] using
      slashC_zhuGC hj ModularGroup.S hz
  have hz0 : z ≠ 0 := by
    exact ne_of_apply_ne Complex.im (zero_im.symm ▸ ne_of_gt hz)
  rw [show (2 * (j : Int)) = ((2 * j : Nat) : Int) by norm_num,
    zpow_neg, zpow_natCast] at hmod
  field_simp [hz0] at hmod
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm] using hmod

/-- The invariant weight-two cell has the precise quasimodular anomaly. -/
theorem spinQAnalytic_pp_one_S {z : Complex} (hz : z ∈ imGT 0) :
    spinQAnalytic SpinPair.pp 1 (-1 / z) =
      z ^ 2 * spinQAnalytic SpinPair.pp 1 z - z / spinTwoPiI := by
  have hzS : -1 / z ∈ imGT 0 := by
    simpa [mobiusC, denomC, spinS00, spinS01, spinS10, spinS11] using
      mobiusC_mem_imGT ModularGroup.S hz
  rw [show (1 : Nat) = 2 * 1 - 1 by omega,
    spinQAnalytic_pp_odd_eq_zhuGC (by norm_num) hzS,
    spinQAnalytic_pp_odd_eq_zhuGC (by norm_num) hz]
  rw [zhuGC_one hzS, zhuGC_one hz]
  rw [show 2 * (Real.pi : Complex) * Complex.I = spinTwoPiI by rfl]
  have hG2 : G2C (-1 / z) * z ^ (-2 : Int) =
      G2C z - spinTwoPiI * z⁻¹ := by
    simpa [slashC, mobiusC, denomC, spinS00, spinS01, spinS10, spinS11,
      spinTwoPiI] using slashC_G2C ModularGroup.S hz
  have hz0 : z ≠ 0 := by
    exact ne_of_apply_ne Complex.im (zero_im.symm ▸ ne_of_gt hz)
  rw [zpow_neg] at hG2
  field_simp [hz0] at hG2
  have hG2' : G2C (-1 / z) = z ^ 2 * G2C z - spinTwoPiI * z := by
    rw [show -1 / z = -(1 / z) by ring]
    linear_combination hG2
  rw [hG2']
  field_simp [spinTwoPiI_ne_zero]

end VOA
