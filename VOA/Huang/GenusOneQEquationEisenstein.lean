import VOA.Huang.GenusOneQEquationAlgebra
import VOA.Modularity.QExpansionBridge
import Mathlib.Analysis.Analytic.OfScalars

/-!
# The actual Eisenstein functions at the q-cusp

The q-variable is independent of τ, including q = 0. Evaluation at qParam τ
is proved to recover the existing analytic Eisenstein functions, with the
normalization factors retained. No Weierstrass identity is assumed here.
-/
namespace VOA.Huang.GenusTwoPoint.QEquation
open VOA Complex
open scoped BigOperators

/-- A convergent scalar power series is analytic at its centre. -/
theorem analyticAt_zero_of_summable (c : ℕ → ℂ) (r : ℝ) (hr : 0 < r)
    (hc : Summable (fun n => ‖c n‖ * r ^ n)) :
    AnalyticAt ℂ (fun q => ∑' n, c n * q ^ n) 0 := by
  let p := FormalMultilinearSeries.ofScalars ℂ c
  have hrad : ENNReal.ofReal r ≤ p.radius := by
    apply p.le_radius_of_summable_norm
    simpa only [p, FormalMultilinearSeries.ofScalars_norm, Real.coe_toNNReal _ hr.le] using hc
  have hp := p.hasFPowerSeriesOnBall
    (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hr) hrad)
  have ha := hp.analyticAt
  convert ha using 1
  funext q
  rw [← FormalMultilinearSeries.ofScalarsSum, FormalMultilinearSeries.ofScalars_sum_eq]
  rfl

/-- Zhu-normalized Eisenstein series in the actual q-coordinate. -/
noncomputable def eisensteinQ (j : ℕ) (q : ℂ) : ℂ :=
  ∑' n : ℕ, zhuG j n * q ^ n

theorem analyticAt_eisensteinQ_zero (j : ℕ) : AnalyticAt ℂ (eisensteinQ j) 0 := by
  apply analyticAt_zero_of_summable _ (1 / 2) (by norm_num)
  exact summable_of_subexponential (fun n => norm_nonneg _) (subexponential_zhuG j)
    (by norm_num) (by norm_num)

theorem eisensteinQ_qParam (j : ℕ) (τ : UpperHalfPlane) :
    eisensteinQ j (qParam τ) = zhuGC j τ := by
  unfold eisensteinQ zhuGC
  apply tsum_congr
  intro n
  rw [qexp_eq_qC_pow, qC_coe]

theorem eisensteinQ_zero (j : ℕ) : eisensteinQ j 0 = zhuG j 0 := by
  unfold eisensteinQ
  rw [tsum_eq_single 0 (fun n hn => by rw [zero_pow hn, mul_zero])]
  simp only [pow_zero, mul_one]

/-- Huang's unnormalized G_(2j), as an analytic germ in q. -/
noncomputable def huangEisensteinQ (j : ℕ) (q : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * I) ^ (2 * j) * eisensteinQ j q

theorem analyticAt_huangEisensteinQ_zero (j : ℕ) :
    AnalyticAt ℂ (huangEisensteinQ j) 0 :=
  analyticAt_const.mul (analyticAt_eisensteinQ_zero j)

/-- Identification with Mathlib's higher normalized Eisenstein modular form. -/
theorem huangEisensteinQ_qParam {j : ℕ} (hj : 2 ≤ j) (τ : UpperHalfPlane) :
    huangEisensteinQ j (qParam τ) =
      (2 * (Real.pi : ℂ) * I) ^ (2 * j) * zhuG j 0 *
        ModularForm.E (show 3 ≤ 2 * j by omega) τ := by
  rw [huangEisensteinQ, eisensteinQ_qParam,
    zhuGC_eq_mul_E hj (coe_mem_imGT_zero τ)]
  ring

/-- The weight-two identification includes the quasimodular series. -/
theorem huangEisensteinQ_one_qParam (τ : UpperHalfPlane) :
    huangEisensteinQ 1 (qParam τ) = G2C τ := by
  rw [huangEisensteinQ, eisensteinQ_qParam, zhuGC_one (coe_mem_imGT_zero τ)]
  have h : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  norm_num only [Nat.mul_one]
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ h, one_pow, one_mul]

/-- The cusp constant is the unnormalized lattice Eisenstein constant. -/
theorem huangEisenstein_constant {j : ℕ} (hj : j ≠ 0) :
    (2 * (Real.pi : ℂ) * I) ^ (2 * j) * zhuG j 0 = 2 * riemannZeta (2 * j) := by
  rw [zhuG_zero, riemannZeta_two_mul_nat hj]
  have hp : (2 : ℂ) ^ (2 * j) = 2 * 2 ^ (2 * j - 1) := by
    conv_lhs => rw [show 2 * j = (2 * j - 1) + 1 by omega]
    rw [pow_succ, mul_comm]
  rw [mul_pow, mul_pow, show I ^ (2 * j) = (-1 : ℂ) ^ j by rw [pow_mul, I_sq], hp,
    pow_succ]
  ring

/-- Identification with the actual lattice sum, not only a normalized form. -/
theorem huangEisensteinQ_eq_lattice {j : ℕ} (hj : 2 ≤ j) (τ : UpperHalfPlane) :
    huangEisensteinQ j (qParam τ) =
      ∑' v : Fin 2 → ℤ, EisensteinSeries.eisSummand (2 * j : ℕ) v τ := by
  rw [huangEisensteinQ_qParam hj,
    tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries (k := 2 * j) (by omega)]
  change _ * ((1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 (2 * j) τ) = _
  rw [huangEisenstein_constant (by omega : j ≠ 0)]
  push_cast
  ring

end VOA.Huang.GenusTwoPoint.QEquation
