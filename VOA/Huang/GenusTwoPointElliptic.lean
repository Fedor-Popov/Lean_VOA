import VOA.Huang.GenusOneQEquationEisenstein
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Cusp regularity of the elliptic Fourier kernels

The q-dependent Lambert tails are analytic at zero, for either orientation of
the multiplicative insertion coordinate. The rational constant terms give the
Fourier models for wp₂ and wp₃ in Huang (2.10). Identification with Mathlib's
lattice-defined Weierstrass functions is NOT proved by this file.
-/
namespace VOA.Huang.GenusTwoPoint.QEquation
open VOA Complex
open scoped BigOperators

noncomputable def lambertTail (c : ℕ → ℂ) (q : ℂ) : ℂ :=
  ∑' n : ℕ, c n * q ^ (n + 1) / (1 - q ^ (n + 1))

/-- A common bound on an entire q-disc, including its centre. -/
theorem lambertTerm_bound (c : ℕ → ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {q : ℂ} (hq : ‖q‖ ≤ r) (n : ℕ) :
    ‖c n * q ^ (n + 1) / (1 - q ^ (n + 1))‖ ≤
      (‖c n‖ * r ^ (n + 1)) / (1 - r) := by
  have hpow : ‖q ^ (n + 1)‖ ≤ r := by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) hq _).trans
      (by rw [pow_succ]; exact mul_le_of_le_one_left hr0 (pow_le_one₀ hr0 hr1.le))
  have hden : 1 - r ≤ ‖(1 : ℂ) - q ^ (n + 1)‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (q ^ (n + 1))
    rw [norm_one] at h
    linarith
  rw [norm_div, norm_mul, norm_pow]
  exact div_le_div₀ (by positivity)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hq _) (norm_nonneg _))
    (by linarith) hden

theorem analyticAt_lambertTail_zero (c : ℕ → ℂ) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1)
    (hc : Summable (fun n => ‖c n‖ * r ^ (n + 1))) :
    AnalyticAt ℂ (lambertTail c) 0 := by
  have hd : DifferentiableOn ℂ (lambertTail c) (Metric.ball 0 r) := by
    apply Complex.differentiableOn_tsum_of_summable_norm (hc.div_const (1 - r))
    · intro n q hq
      have hqr : ‖q‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using hq
      have hn : 1 - q ^ (n + 1) ≠ 0 := by
        have hpow : ‖q ^ (n + 1)‖ < 1 := by
          rw [norm_pow]
          exact pow_lt_one₀ (norm_nonneg _) (hqr.trans hr1) (by omega)
        intro he
        rw [← sub_eq_zero.mp he, norm_one] at hpow
        exact lt_irrefl _ hpow
      exact ((differentiableAt_const (c n)).mul ((differentiableAt_id).pow (n + 1))).div
        ((differentiableAt_const (1 : ℂ)).sub ((differentiableAt_id).pow (n + 1))) hn
        |>.differentiableWithinAt
    · exact Metric.isOpen_ball
    · intro n q hq
      apply lambertTerm_bound c hr0.le hr1
      exact (by simpa [Metric.mem_ball, dist_zero_right] using hq : ‖q‖ < r).le
  exact hd.analyticAt (Metric.isOpen_ball.mem_nhds (by simpa using hr0))

/-- The total series definition is an actual sum throughout the bounded disc. -/
theorem hasSum_lambertTail (c : ℕ → ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hc : Summable (fun n => ‖c n‖ * r ^ (n + 1))) {q : ℂ} (hq : ‖q‖ ≤ r) :
    HasSum (fun n => c n * q ^ (n + 1) / (1 - q ^ (n + 1))) (lambertTail c q) :=
  (Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (lambertTerm_bound c hr0 hr1 hq) (hc.div_const (1 - r)))).hasSum

theorem lambertTail_zero (c : ℕ → ℂ) : lambertTail c 0 = 0 := by
  simp [lambertTail]

/-- The numerator coefficients of the positive-q elliptic tail. -/
noncomputable def ellipticCoeff (m : ℕ) (x : ℂ) (n : ℕ) : ℂ :=
  (n + 1 : ℂ) ^ m * (x ^ (n + 1) - (-1 : ℂ) ^ m * (x⁻¹) ^ (n + 1))

theorem summable_ellipticCoeff (m : ℕ) (x : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hx : r * ‖x‖ < 1) (hxi : r * ‖x⁻¹‖ < 1) :
    Summable (fun n => ‖ellipticCoeff m x n‖ * r ^ (n + 1)) := by
  have hg (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
      Summable (fun n : ℕ => (n + 1 : ℝ) ^ m * t ^ (n + 1)) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (r := t) m
      (by simpa only [Real.norm_eq_abs, abs_of_nonneg ht0] using ht1)
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h
  have hs := (hg (r * ‖x‖) (by positivity) hx).add
    (hg (r * ‖x⁻¹‖) (by positivity) hxi)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  have hb : ‖ellipticCoeff m x n‖ ≤
      (n + 1 : ℝ) ^ m * (‖x‖ ^ (n + 1) + ‖x⁻¹‖ ^ (n + 1)) := by
    unfold ellipticCoeff
    rw [norm_mul, norm_pow, show ‖(n + 1 : ℂ)‖ = (n + 1 : ℝ) by
      simpa using Complex.norm_natCast (n + 1)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [norm_pow, norm_mul, norm_neg, norm_one, one_pow, one_mul]
      using norm_sub_le (x ^ (n + 1)) ((-1 : ℂ) ^ m * (x⁻¹) ^ (n + 1))
  calc
    _ ≤ ((n + 1 : ℝ) ^ m * (‖x‖ ^ (n + 1) + ‖x⁻¹‖ ^ (n + 1))) * r ^ (n + 1) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _ = _ := by simp only [mul_pow]; ring

/-- Both orientations have a positive q-radius; no |x| < 1 assumption. -/
theorem analyticAt_ellipticTail_zero (m : ℕ) (x : ℂ) :
    AnalyticAt ℂ (lambertTail (ellipticCoeff m x)) 0 := by
  let d : ℝ := 2 * (1 + ‖x‖ + ‖x⁻¹‖)
  have hd : 0 < d := by dsimp [d]; positivity
  have hr : 0 < d⁻¹ := inv_pos.mpr hd
  have he : d⁻¹ * d = 1 := inv_mul_cancel₀ hd.ne'
  have h1 : d⁻¹ < 1 := by
    dsimp [d] at he
    nlinarith [norm_nonneg x, norm_nonneg x⁻¹]
  have hx : d⁻¹ * ‖x‖ < 1 := by
    dsimp [d] at he
    nlinarith [mul_nonneg hr.le (norm_nonneg x⁻¹)]
  have hxi : d⁻¹ * ‖x⁻¹‖ < 1 := by
    dsimp [d] at he
    nlinarith [mul_nonneg hr.le (norm_nonneg x)]
  exact analyticAt_lambertTail_zero _ hr h1 (summable_ellipticCoeff m x hr.le hx hxi)

/-- Fourier expression for wp₂, with x = exp(2πiz). -/
noncomputable def wpTwoQ (x q : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * I) ^ 2 *
    (x / (1 - x) ^ 2 + lambertTail (ellipticCoeff 1 x) q) - huangEisensteinQ 1 q

/-- Fourier expression for wp₃ = -(1/2) ∂z wp₂. -/
noncomputable def wpThreeQ (x q : ℂ) : ℂ :=
  -((2 * (Real.pi : ℂ) * I) ^ 3 / 2) *
    (x * (1 + x) / (1 - x) ^ 3 + lambertTail (ellipticCoeff 2 x) q)

theorem analyticAt_wpTwoQ_zero (x : ℂ) : AnalyticAt ℂ (wpTwoQ x) 0 :=
  (analyticAt_const.mul (analyticAt_const.add (analyticAt_ellipticTail_zero 1 x))).sub
    (analyticAt_huangEisensteinQ_zero 1)

theorem analyticAt_wpThreeQ_zero (x : ℂ) : AnalyticAt ℂ (wpThreeQ x) 0 :=
  analyticAt_const.mul (analyticAt_const.add (analyticAt_ellipticTail_zero 2 x))

/-- Opposite insertion orientations use the same even Fourier kernel. -/
theorem wpTwoQ_inv {x : ℂ} (hx : x ≠ 0) (q : ℂ) : wpTwoQ x⁻¹ q = wpTwoQ x q := by
  have ht : ellipticCoeff 1 x⁻¹ = ellipticCoeff 1 x := by
    funext n
    simp only [ellipticCoeff, inv_inv, pow_one, neg_mul, one_mul, sub_neg_eq_add]
    ring
  have hc : x⁻¹ / (1 - x⁻¹) ^ 2 = x / (1 - x) ^ 2 := by
    by_cases h1 : x = 1
    · simp [h1]
    · field_simp [hx, sub_ne_zero.mpr h1, sub_ne_zero.mpr (Ne.symm h1)]
      ring
  simp only [wpTwoQ, ht, hc]

/-- Opposite insertion orientations negate the odd Fourier kernel. -/
theorem wpThreeQ_inv {x : ℂ} (hx : x ≠ 0) (q : ℂ) :
    wpThreeQ x⁻¹ q = -wpThreeQ x q := by
  have ht : ellipticCoeff 2 x⁻¹ = -ellipticCoeff 2 x := by
    funext n
    simp only [ellipticCoeff, inv_inv, even_two.neg_pow, one_pow, one_mul, Pi.neg_apply]
    ring
  have hl : lambertTail (-ellipticCoeff 2 x) q = -lambertTail (ellipticCoeff 2 x) q := by
    simp only [lambertTail, Pi.neg_apply, neg_mul, neg_div, tsum_neg]
  have hc : x⁻¹ * (1 + x⁻¹) / (1 - x⁻¹) ^ 3 = -(x * (1 + x) / (1 - x) ^ 3) := by
    by_cases h1 : x = 1
    · simp [h1]
    · field_simp [hx, sub_ne_zero.mpr h1, sub_ne_zero.mpr (Ne.symm h1)]
      ring
  simp only [wpThreeQ, ht, hl, hc]
  ring

/-- The four concrete Fourier generators of the elliptic coefficient algebra. -/
noncomputable def ellipticGenerators (x : ℂ) : Fin 4 → ℂ → ℂ :=
  ![huangEisensteinQ 2, huangEisensteinQ 3, wpTwoQ x, wpThreeQ x]

theorem analyticAt_ellipticGenerators_zero (x : ℂ) (i : Fin 4) :
    AnalyticAt ℂ (ellipticGenerators x i) 0 := by
  fin_cases i
  · exact analyticAt_huangEisensteinQ_zero 2
  · exact analyticAt_huangEisensteinQ_zero 3
  · exact analyticAt_wpTwoQ_zero x
  · exact analyticAt_wpThreeQ_zero x

theorem elliptic_coefficient_analyticAt_zero (x : ℂ)
    (c : coefficientAlgebra (ellipticGenerators x)) : AnalyticAt ℂ c.val 0 :=
  coefficient_analyticAt_zero _ (analyticAt_ellipticGenerators_zero x) c

end VOA.Huang.GenusTwoPoint.QEquation
