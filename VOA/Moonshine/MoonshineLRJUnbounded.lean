import VOA.Moonshine.JAnalyticQExpansion
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The coefficients of `J` are unbounded

Blueprint: coefficient unboundedness in `MOON_M8_LEAN.md`.

`JShift = Σ aₙ qⁿ` is the `q`-expansion of `q · (j − 744)`, with `a₀ = 1`.  If `‖aₙ‖ ≤ C` for all
`n`, write `F(z) = q · (j(z) − 744)` and compare `z = iY` with `w = S·z = i/Y`:
* at `z`, `‖F(z) − 1‖ ≤ C s/(1 − s)` with `s = e^{−2πY}`, so `‖F(z)‖ ≥ 1 − 2Cs`;
* `j(w) = j(z)`, so `‖F(z)‖ = (s/t) ‖F(w)‖ ≤ (s/t) · C/(1 − t)` with `t = e^{−2π/Y}`.
For large `Y` the second bound is about `C Y e^{−2πY}`, which is incompatible with the first.

Main result: `JShift_coeff_unbounded : ¬ ∃ C : ℝ, ∀ n, ‖PowerSeries.coeff n JShift‖ ≤ C`.
-/

namespace VOA.Moonshine.ConwayNorton.M8

open UpperHalfPlane Real

/-- With bounded coefficients, `‖q (j(z) − 744)‖ ≤ C / (1 − |q|)`. -/
theorem norm_qJ_le_of_bounded {C : ℝ} (hC : ∀ n, ‖PowerSeries.coeff n JShift‖ ≤ C) (z : ℍ) :
    ‖Function.Periodic.qParam 1 (z : ℂ) * (jInvariant z - 744)‖ ≤
      C * (1 - Real.exp (-2 * π * z.im))⁻¹ := by
  have hq : ‖Function.Periodic.qParam 1 (z : ℂ)‖ = Real.exp (-2 * π * z.im) :=
    Moonshine.norm_qFun z
  have hs0 : 0 ≤ Real.exp (-2 * π * z.im) := (Real.exp_pos _).le
  have hs1 : Real.exp (-2 * π * z.im) < 1 := by
    rw [Real.exp_lt_one_iff]
    have := z.im_pos
    nlinarith [Real.pi_pos]
  refine (Moonshine.hasSum_JShift z).norm_le_of_bounded
    ((hasSum_geometric_of_lt_one hs0 hs1).mul_left C) fun n => ?_
  rw [norm_mul, norm_pow, hq]
  exact mul_le_mul_of_nonneg_right (hC n) (pow_nonneg hs0 n)

/-- With bounded coefficients, `‖q (j(z) − 744) − 1‖ ≤ C |q| / (1 − |q|)`. -/
theorem norm_qJ_sub_one_le_of_bounded {C : ℝ} (hC : ∀ n, ‖PowerSeries.coeff n JShift‖ ≤ C)
    (z : ℍ) :
    ‖Function.Periodic.qParam 1 (z : ℂ) * (jInvariant z - 744) - 1‖ ≤
      C * Real.exp (-2 * π * z.im) * (1 - Real.exp (-2 * π * z.im))⁻¹ := by
  have hq : ‖Function.Periodic.qParam 1 (z : ℂ)‖ = Real.exp (-2 * π * z.im) :=
    Moonshine.norm_qFun z
  set s := Real.exp (-2 * π * z.im)
  have hs0 : 0 ≤ s := (Real.exp_pos _).le
  have hs1 : s < 1 := by
    rw [Real.exp_lt_one_iff]
    have := z.im_pos
    nlinarith [Real.pi_pos]
  have h := (hasSum_nat_add_iff' 1).mpr (Moonshine.hasSum_JShift z)
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_JShift] at h
  refine h.norm_le_of_bounded ((hasSum_geometric_of_lt_one hs0 hs1).mul_left (C * s)) fun n => ?_
  rw [norm_mul, norm_pow, hq, pow_succ]
  have := mul_le_mul_of_nonneg_right (hC (n + 1)) (mul_nonneg (pow_nonneg hs0 n) hs0)
  linarith

theorem one_le_two_mul_pi_sq : 1 ≤ 2 * π ^ 2 := by nlinarith [Real.pi_gt_three]

/-- **The coefficients of `J` are unbounded.** -/
theorem JShift_coeff_unbounded : ¬ ∃ C : ℝ, ∀ n, ‖PowerSeries.coeff n JShift‖ ≤ C := by
  rintro ⟨C, hC⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  set E := Real.exp (2 * π) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  set K := 2 * C + 2 * C * E with hK
  have hK0 : 0 ≤ K := by positivity
  set Y := K + 1 with hY
  have hY1 : 1 ≤ Y := by linarith
  have hYpos : 0 < Y := by linarith
  -- the points `z = iY` and `w = S • z = i/Y`
  let z : ℍ := ⟨Complex.I * Y, by simp [hYpos]⟩
  have hzim : z.im = Y := by simp [z, UpperHalfPlane.im]
  set w := ModularGroup.S • z with hw
  have hwim : w.im = 1 / Y := by
    rw [hw, modular_S_smul]
    simp only [UpperHalfPlane.im, Complex.inv_im, Complex.neg_im, Complex.normSq_apply]
    simp [z]
  have hj : jInvariant w = jInvariant z := VOA.jInvariant_smul ModularGroup.S z
  set s := Real.exp (-2 * π * Y) with hs
  set t := Real.exp (-2 * π * (1 / Y)) with ht
  have hs0 : 0 < s := Real.exp_pos _
  have ht0 : 0 < t := Real.exp_pos _
  -- the two bounds
  have hupper := norm_qJ_le_of_bounded hC w
  have hlower := norm_qJ_sub_one_le_of_bounded hC z
  rw [hwim, ← ht, hj] at hupper
  rw [hzim, ← hs] at hlower
  have hqz : ‖Function.Periodic.qParam 1 (z : ℂ)‖ = s := by
    have := Moonshine.norm_qFun z
    rw [hzim] at this
    exact this
  have hqw : ‖Function.Periodic.qParam 1 (w : ℂ)‖ = t := by
    have := Moonshine.norm_qFun w
    rw [hwim] at this
    exact this
  set a := ‖jInvariant z - 744‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  rw [norm_mul, hqw] at hupper
  -- `s ≤ 1/2`
  have hs_half : s ≤ 1 / 2 := by
    have h1 : 2 * π * Y + 1 ≤ Real.exp (2 * π * Y) := Real.add_one_le_exp _
    have h2 : s * Real.exp (2 * π * Y) = 1 := by
      rw [hs, ← Real.exp_add]
      simp
    have h3 : 1 ≤ 2 * π * Y := by nlinarith [Real.pi_gt_three]
    nlinarith
  -- lower bound: `s a ≥ 1 − 2 C s`
  have hlow : 1 - 2 * C * s ≤ s * a := by
    have h1 := norm_sub_norm_le (1 : ℂ)
      (Function.Periodic.qParam 1 (z : ℂ) * (jInvariant z - 744))
    rw [norm_sub_rev, norm_one, norm_mul, hqz] at h1
    have h1' : 1 - s * a ≤ C * s * (1 - s)⁻¹ := le_trans h1 hlower
    have h2 : C * s * (1 - s)⁻¹ ≤ 2 * C * s := by
      rw [mul_inv_le_iff₀ (by linarith)]
      have : 0 ≤ C * s * (1 - 2 * s) := mul_nonneg (mul_nonneg hC0 hs0.le) (by linarith)
      linarith
    linarith
  -- upper bound on `t a`: `C / (1 − t) ≤ C (1 + Y)`
  have hx : 0 < 2 * π * (1 / Y) := by positivity
  have htx : t * (1 + 2 * π * (1 / Y)) ≤ 1 := by
    have h1 : 2 * π * (1 / Y) + 1 ≤ Real.exp (2 * π * (1 / Y)) := Real.add_one_le_exp _
    have h2 : t * Real.exp (2 * π * (1 / Y)) = 1 := by
      rw [ht, ← Real.exp_add]
      simp
    nlinarith
  have ht1 : t < 1 := by
    have : 0 < t * (2 * π * (1 / Y)) := by positivity
    nlinarith
  have hxY : 2 * π * (1 / Y) * Y = 2 * π := by field_simp
  have hY1t : 1 ≤ (1 + Y) * (1 - t) := by
    have h1 : t * Y + t * (2 * π) ≤ Y := by
      have := mul_le_mul_of_nonneg_right htx hYpos.le
      nlinarith
    nlinarith [Real.pi_gt_three]
  have hta : t * a ≤ C * (1 + Y) := by
    have h1 : C * (1 - t)⁻¹ ≤ C * (1 + Y) := by
      rw [mul_inv_le_iff₀ (by linarith)]
      nlinarith
    linarith
  -- `t ≥ e^{−2π}`, i.e. `t E ≥ 1`
  have htE : 1 ≤ t * E := by
    rw [ht, hE, ← Real.exp_add]
    apply Real.one_le_exp
    have : 2 * π * (1 / Y) ≤ 2 * π := by
      rw [mul_one_div]
      exact div_le_self (by positivity) hY1
    linarith
  -- combine: `s a ≤ s C (1 + Y) E`
  have hsa : s * a ≤ s * (C * (1 + Y) * E) := by
    have h1 : s * a ≤ s * a * (t * E) := le_mul_of_one_le_right (by positivity) htE
    have h2 : s * a * (t * E) = s * E * (t * a) := by ring
    have h3 : s * E * (t * a) ≤ s * E * (C * (1 + Y)) :=
      mul_le_mul_of_nonneg_left hta (by positivity)
    have h4 : s * E * (C * (1 + Y)) = s * (C * (1 + Y) * E) := by ring
    linarith
  -- so `1 ≤ s (2C + C (1+Y) E)`, hence `e^{2πY} ≤ 2C + C (1+Y) E ≤ K Y`
  set X := 2 * C + C * (1 + Y) * E with hX
  have h4 : 1 ≤ s * X := by
    have : s * X = 2 * C * s + s * (C * (1 + Y) * E) := by rw [hX]; ring
    linarith
  set B := Real.exp (2 * π * Y) with hB
  have hsB : s * B = 1 := by
    rw [hs, hB, ← Real.exp_add]
    simp
  have hB0 : 0 ≤ B := (Real.exp_pos _).le
  have h5 : B ≤ X := by
    have := mul_le_mul_of_nonneg_left h4 hB0
    have e : B * (s * X) = (s * B) * X := by ring
    rw [e, hsB] at this
    linarith
  have h6 : X ≤ K * Y := by
    have e : K * Y - X = 2 * C * (Y - 1) + C * E * (Y - 1) := by rw [hK, hX]; ring
    have h1 : 0 ≤ 2 * C * (Y - 1) := mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ C * E * (Y - 1) := mul_nonneg (by positivity) (by linarith)
    linarith
  -- but `e^{2πY} ≥ (2πY)²/2 ≥ Y² > K Y`
  have hquad : 1 + 2 * π * Y + (2 * π * Y) ^ 2 / 2 ≤ B :=
    Real.quadratic_le_exp_of_nonneg (by positivity)
  have hpi : 1 ≤ 2 * π ^ 2 := one_le_two_mul_pi_sq
  have h7 : Y * Y ≤ (2 * π * Y) ^ 2 / 2 := by
    have e : (2 * π * Y) ^ 2 / 2 = (2 * π ^ 2) * (Y * Y) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_right hpi (mul_nonneg hYpos.le hYpos.le)
    linarith
  have h8 : K * Y < Y * Y := mul_lt_mul_of_pos_right (by linarith) hYpos
  have h9 : 0 ≤ 2 * π * Y := by positivity
  linarith

end VOA.Moonshine.ConwayNorton.M8
