/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.CommutativityTarget
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
# Commutativity as analytic continuation

`CommutativityTarget.CommutativityHalfReal` identifies, on the real segment `2/3 < t < 1`, the
product `⟨f, 𝒴₁(w₁,1)𝒴₂(w₂,t)w₃⟩` with a finite sum of iterates
`G_j(t) = ⟨f, 𝒴₃ʲ(𝒴̃ʲ(w₂, t−1)w₁, 1)w₃⟩` taken with the `e^{πi}` branch of `t − 1 < 0`.  Here we
upgrade this to the genuine **analytic continuation** statement on the upper half plane:

`commutativityHalf_of_halfReal`: for every complex `x` with `Im x > 0`, `‖x − 1‖ < 1/3`,
`‖x‖ < 1`, the product equals `Σ_j G_j(x)` with the **principal** power of `x − 1`; and
`analyticOnNhd_iterValue_upper`: each `G_j` is holomorphic on the whole upper half disc
`{Im x > 0, ‖x − 1‖ < 1}`, which crosses the circle `|x| = 1`.

So the product, holomorphic on `|x| < 1`, continues through the upper half plane to the region
`|x| > 1` as `Σ_j G_j`, and (`CommutativityTarget.CommutativityInputReal`) on `1 < x < 2` the
continuation is a finite sum of products in the opposite order.

## Proof
* power series with radius `≥ 1` are analytic on the unit disc (`analyticOnNhd_tsum_pow`);
* the product is `x^{−ν−1} · Σ_k c_k xᵏ`, the iterate is `(x−1)^{s₀} · Σ_p d_p (x−1)ᵖ`
  (`tsum_cpow_shift`), with absolutely convergent series for `|x| < 1`, `|x − 1| < 1`
  (`AssocTarget`/`HuangODEContra` summability);
* the modified iterate `H_j(x) = e^{πis₀}(1−x)^{s₀} · Σ_p d_p (x−1)ᵖ` is holomorphic near the real
  segment, equals `G_j` on the segment (`neg_cpow_real`) and on the upper half plane
  (`neg_cpow_of_im_neg`); the identity theorem on the convex set `ball 1 (1/3) ∩ ball 0 1` does
  the rest.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.CommutativityTarget

open VOA VOA.SkewIntertwiner VOA.Huang.MatrixCoeff VOA.Huang.AssocTarget
open VOA.Huang.BraidingSkew
open Complex Filter Topology
open scoped BigOperators

universe u

/-! ## Analytic preliminaries -/

/-- A power series that converges absolutely at every radius `< 1` is analytic on the unit
disc. -/
theorem analyticOnNhd_tsum_pow (c : ℕ → ℂ)
    (hc : ∀ r : ℝ, 0 < r → r < 1 → Summable fun k => ‖c k‖ * r ^ k) :
    AnalyticOnNhd ℂ (fun x => ∑' k, c k * x ^ k) (Metric.ball 0 1) := by
  set p := FormalMultilinearSeries.ofScalars ℂ c
  have hrad : (1 : ENNReal) ≤ p.radius := by
    refine ENNReal.le_of_forall_pos_nnreal_lt fun r hr0 hr1 => ?_
    have hr1' : (r : ℝ) < 1 := by exact_mod_cast hr1
    refine p.le_radius_of_summable_norm ?_
    refine (hc r (by exact_mod_cast hr0) hr1').congr fun n => ?_
    rw [FormalMultilinearSeries.ofScalars_norm]
  have hp := p.hasFPowerSeriesOnBall (lt_of_lt_of_le zero_lt_one hrad)
  have ha := hp.analyticOnNhd
  intro x hx
  have hx' : x ∈ Metric.eball (0 : ℂ) p.radius := by
    refine Metric.eball_subset_eball hrad ?_
    simpa [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm] using hx
  have := ha x hx'
  convert this using 1
  funext y
  rw [← FormalMultilinearSeries.ofScalarsSum, FormalMultilinearSeries.ofScalars_sum_eq]
  rfl

/-- `(−w)^s = w^s e^{πis}` when `Im w < 0`. -/
theorem neg_cpow_of_im_neg {w : ℂ} (hw : w.im < 0) (s : ℂ) :
    (-w) ^ s = w ^ s * Complex.exp (↑Real.pi * Complex.I * s) := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hw0' : -w ≠ 0 := neg_ne_zero.mpr hw0
  rw [Complex.cpow_def_of_ne_zero hw0', Complex.cpow_def_of_ne_zero hw0, ← Complex.exp_add]
  congr 1
  have : Complex.log (-w) = Complex.log w + Real.pi * Complex.I := by
    rw [Complex.log, Complex.log, norm_neg, arg_neg_eq_arg_add_pi_of_im_neg hw]
    push_cast; ring
  rw [this]; ring

/-- `Σ_k c_k z^{−(ν−k)−1} = z^{−ν−1} Σ_k c_k zᵏ` for `z ≠ 0`. -/
theorem tsum_cpow_shift (c : ℕ → ℂ) (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    ∑' k : ℕ, c k * z ^ (-(ν - k) - 1) = z ^ (-ν - 1) * ∑' k : ℕ, c k * z ^ k := by
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [show -(ν - (k : ℂ)) - 1 = (-ν - 1) + k by ring, Complex.cpow_add _ _ hz,
    Complex.cpow_natCast]
  ring

/-- From absolute convergence of `Σ c_k r^{−(ν−k)−1}` to that of `Σ ‖c_k‖ rᵏ`. -/
theorem summable_norm_mul_pow_of (c : ℕ → ℂ) (ν : ℂ) {r : ℝ} (hr : 0 < r)
    (h : Summable fun k : ℕ => ‖c k * (r : ℂ) ^ (-(ν - k) - 1)‖) :
    Summable fun k => ‖c k‖ * r ^ k := by
  refine (h.div_const (r ^ (-ν.re - 1))).congr fun k => ?_
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hr, re_aux',
    show -ν.re + (k : ℝ) - 1 = (-ν.re - 1) + k by ring, Real.rpow_add hr, Real.rpow_natCast]
  have : 0 < r ^ (-ν.re - 1) := Real.rpow_pos_of_pos hr _
  field_simp

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-! ## The product side -/

section Product

variable {P₁ P₂ P₃ P₄ Q : LWModule W}
  {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
  {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
  {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier} {f : P₄.carrier →ₗ[ℂ] ℂ}

/-- The product at `z₁ = 1` as `x^{−ν−1}` times a power series. -/
theorem prodValue_one (σ ν : ℂ) {x : ℂ} (hx : x ≠ 0) :
    prodValue Y₁ Y₂ f w₁ w₂ w₃ σ ν 1 x
      = x ^ (-ν - 1) * ∑' k : ℕ, prodCoeff Y₁ Y₂ f w₁ w₂ w₃ (σ - ν + k) (ν - k) * x ^ k := by
  rw [prodValue, ← tsum_cpow_shift _ ν hx]
  refine tsum_congr fun k => ?_
  rw [Complex.one_cpow, mul_one]

/-- The analytic model of the product: `x^{−ν−1} · Σ_k c_k xᵏ`. -/
noncomputable def prodModel (σ ν : ℂ) (x : ℂ) : ℂ :=
  x ^ (-ν - 1) * ∑' k : ℕ, prodCoeff Y₁ Y₂ f w₁ w₂ w₃ (σ - ν + k) (ν - k) * x ^ k

theorem analyticOnNhd_prodModel (hV : StronglyRational W) (i₁ : P₁.IsIrreducibleLW)
    (i₂ : P₂.IsIrreducibleLW) (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
    (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)
    {α₁ α₂ α₃ h₄ : ℂ} (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄) :
    AnalyticOnNhd ℂ (prodModel (Y₁ := Y₁) (Y₂ := Y₂) (f := f) (w₁ := w₁) (w₂ := w₂) (w₃ := w₃)
        (α₁ + α₂ + α₃ - h₄ - 2) (α₂ + α₃ - 1 - Q.h))
      (Metric.ball 0 1 ∩ {x | 0 < x.re}) := by
  have hS : AnalyticOnNhd ℂ (fun x => ∑' k : ℕ, prodCoeff Y₁ Y₂ f w₁ w₂ w₃
      ((α₁ + α₂ + α₃ - h₄ - 2) - (α₂ + α₃ - 1 - Q.h) + k) ((α₂ + α₃ - 1 - Q.h) - k) * x ^ k)
      (Metric.ball 0 1) := by
    refine analyticOnNhd_tsum_pow _ fun r hr0 hr1 => ?_
    have := VOA.Huang.HuangODEContra.summable_prodTerm_of_moduleC2Input
      VOA.Huang.BuhlSpanning.moduleC2Input_holds hV i₁ i₂ i₃ i₄ Q.isMod hY₁ hY₂ h₁ h₂ h₃ hf
      (isBase_canonical Q hY₂ h₂ h₃) (z₁ := 1) (z₂ := (r : ℂ)) (by exact_mod_cast hr0.ne')
      (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, norm_one]; exact hr1)
    refine summable_norm_mul_pow_of _ (α₂ + α₃ - 1 - Q.h) hr0 (this.congr fun k => ?_)
    rw [Complex.one_cpow, mul_one]
  intro x hx
  refine (AnalyticAt.cpow analyticAt_id analyticAt_const ?_).mul (hS x hx.1)
  exact Complex.mem_slitPlane_iff.2 (Or.inl hx.2)

end Product

/-! ## The iterate side -/

section Iterate

variable {P₁ P₂ P₃ P₄ R : LWModule W}
  {Y₃ : IntertwiningModes R.carrier P₃.carrier P₄.carrier}
  {Yt : IntertwiningModes P₂.carrier P₁.carrier R.carrier}
  {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier} {f : P₄.carrier →ₗ[ℂ] ℂ}

/-- The iterate at outer point `1`, inner point `z`, as `z^{−ν−1}` times a power series. -/
theorem iterValue_one (σ ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    iterValue Y₃ Yt f w₂ w₁ w₃ σ ν z 1
      = z ^ (-ν - 1) * ∑' p : ℕ, iterCoeff Y₃ Yt f w₂ w₁ w₃ (ν - p) (σ - ν + p) * z ^ p := by
  rw [iterValue, ← tsum_cpow_shift _ ν hz]
  refine tsum_congr fun k => ?_
  rw [Complex.one_cpow, mul_one]

/-- The power series of the iterate, analytic on the unit disc. -/
theorem analyticOnNhd_iterSeries (hV : StronglyRational W) (i₁ : P₁.IsIrreducibleLW)
    (i₂ : P₂.IsIrreducibleLW) (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    (hY₃ : IsIntertwiningOperator R.isMod P₃.isMod P₄.isMod Y₃)
    (hYt : IsIntertwiningOperator P₂.isMod P₁.isMod R.isMod Yt)
    {α₁ α₂ α₃ h₄ : ℂ} (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄) :
    AnalyticOnNhd ℂ (fun z => ∑' p : ℕ, iterCoeff Y₃ Yt f w₂ w₁ w₃ ((α₁ + α₂ - 1 - R.h) - p)
        ((α₁ + α₂ + α₃ - h₄ - 2) - (α₁ + α₂ - 1 - R.h) + p) * z ^ p) (Metric.ball 0 1) := by
  refine analyticOnNhd_tsum_pow _ fun r hr0 hr1 => ?_
  have hb : IsBase Yt w₂ w₁ (α₁ + α₂ - 1 - R.h) := by
    have := isBase_canonical R hYt h₂ h₁
    rwa [show α₂ + α₁ - 1 - R.h = α₁ + α₂ - 1 - R.h by ring] at this
  have := VOA.Huang.HuangODEContra.summable_iterTerm_of_moduleC2Input
    VOA.Huang.BuhlSpanning.moduleC2Input_holds hV i₂ i₁ i₃ i₄ R.isMod hY₃ hYt h₂ h₁ h₃ hf hb
    (z₀ := (r : ℂ)) (z₂ := 1) (by exact_mod_cast hr0.ne')
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, norm_one]; exact hr1)
  refine summable_norm_mul_pow_of _ (α₁ + α₂ - 1 - R.h) hr0 (this.congr fun k => ?_)
  rw [Complex.one_cpow, mul_one, show α₂ + α₁ + α₃ - h₄ - 2 = α₁ + α₂ + α₃ - h₄ - 2 by ring]

/-- **The iterate `G(x) = ⟨f, 𝒴₃(𝒴̃(w₂, x−1)w₁, 1)w₃⟩` is holomorphic on the upper half
disc** `{Im x > 0, ‖x − 1‖ < 1}` (which crosses the unit circle). -/
theorem analyticOnNhd_iterValue_upper (hV : StronglyRational W) (i₁ : P₁.IsIrreducibleLW)
    (i₂ : P₂.IsIrreducibleLW) (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    (hY₃ : IsIntertwiningOperator R.isMod P₃.isMod P₄.isMod Y₃)
    (hYt : IsIntertwiningOperator P₂.isMod P₁.isMod R.isMod Yt)
    {α₁ α₂ α₃ h₄ : ℂ} (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄) :
    AnalyticOnNhd ℂ (fun x => iterValue Y₃ Yt f w₂ w₁ w₃ (α₁ + α₂ + α₃ - h₄ - 2)
        (α₁ + α₂ - 1 - R.h) (x - 1) 1) {x | 0 < x.im ∧ ‖x - 1‖ < 1} := by
  have hS := analyticOnNhd_iterSeries hV i₁ i₂ i₃ i₄ hY₃ hYt h₁ h₂ h₃ hf
  have hopen : IsOpen {x : ℂ | 0 < x.im ∧ ‖x - 1‖ < 1} :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const)
  intro x hx
  have hmodel : AnalyticAt ℂ (fun x : ℂ => (x - 1) ^ (-(α₁ + α₂ - 1 - R.h) - 1)
      * ∑' p : ℕ, iterCoeff Y₃ Yt f w₂ w₁ w₃ ((α₁ + α₂ - 1 - R.h) - p)
        ((α₁ + α₂ + α₃ - h₄ - 2) - (α₁ + α₂ - 1 - R.h) + p) * (x - 1) ^ p) x := by
    refine AnalyticAt.mul ?_ ?_
    · refine AnalyticAt.cpow (analyticAt_id.sub analyticAt_const) analyticAt_const ?_
      refine Complex.mem_slitPlane_iff.2 (Or.inr ?_)
      simp only [Complex.sub_im, Complex.one_im, sub_zero]
      exact hx.1.ne'
    · have hx1 : x - 1 ∈ Metric.ball (0 : ℂ) 1 := by
        simpa [Metric.mem_ball, dist_zero_right] using hx.2
      exact AnalyticAt.comp (f := fun y : ℂ => y - 1) (hS (x - 1) hx1)
        (analyticAt_id.sub analyticAt_const)
  refine hmodel.congr ?_
  filter_upwards [hopen.mem_nhds hx] with y hy
  have hy0 : y - 1 ≠ 0 := fun h => by
    have := hy.1
    rw [show y = 1 by linear_combination h] at this
    simp at this
  rw [iterValue_one _ _ hy0]

end Iterate

/-! ## The modified iterate, holomorphic across the real segment -/

section Model

variable {P₁ P₂ P₃ P₄ R : LWModule W}
  {Y₃ : IntertwiningModes R.carrier P₃.carrier P₄.carrier}
  {Yt : IntertwiningModes P₂.carrier P₁.carrier R.carrier}
  {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier} {f : P₄.carrier →ₗ[ℂ] ℂ}

/-- The iterate with the branch cut moved to `x ≥ 1`:
`H(x) = e^{πis₀}(1−x)^{s₀} Σ_p d_p (x−1)ᵖ`, `s₀ = −ν−1`. -/
noncomputable def iterModel (σ ν : ℂ) (x : ℂ) : ℂ :=
  Complex.exp (↑Real.pi * Complex.I * (-ν - 1)) * (1 - x) ^ (-ν - 1)
    * ∑' p : ℕ, iterCoeff Y₃ Yt f w₂ w₁ w₃ (ν - p) (σ - ν + p) * (x - 1) ^ p

theorem analyticOnNhd_iterModel (hV : StronglyRational W) (i₁ : P₁.IsIrreducibleLW)
    (i₂ : P₂.IsIrreducibleLW) (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    (hY₃ : IsIntertwiningOperator R.isMod P₃.isMod P₄.isMod Y₃)
    (hYt : IsIntertwiningOperator P₂.isMod P₁.isMod R.isMod Yt)
    {α₁ α₂ α₃ h₄ : ℂ} (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄) :
    AnalyticOnNhd ℂ (iterModel (Y₃ := Y₃) (Yt := Yt) (f := f) (w₁ := w₁) (w₂ := w₂) (w₃ := w₃)
        (α₁ + α₂ + α₃ - h₄ - 2) (α₁ + α₂ - 1 - R.h)) {x | ‖x - 1‖ < 1 ∧ 0 < (1 - x).re} := by
  have hS := analyticOnNhd_iterSeries hV i₁ i₂ i₃ i₄ hY₃ hYt h₁ h₂ h₃ hf
  intro x hx
  refine AnalyticAt.mul (AnalyticAt.mul analyticAt_const ?_) ?_
  · exact AnalyticAt.cpow (analyticAt_const.sub analyticAt_id) analyticAt_const
      (Complex.mem_slitPlane_iff.2 (Or.inl hx.2))
  · have hx1 : x - 1 ∈ Metric.ball (0 : ℂ) 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hx.1
    exact AnalyticAt.comp (f := fun y : ℂ => y - 1) (hS (x - 1) hx1)
      (analyticAt_id.sub analyticAt_const)

/-- On the upper half plane the modified iterate is the iterate (principal branch). -/
theorem iterModel_eq_of_im_pos (σ ν : ℂ) {x : ℂ} (hx : 0 < x.im) :
    iterModel (Y₃ := Y₃) (Yt := Yt) (f := f) (w₁ := w₁) (w₂ := w₂) (w₃ := w₃) σ ν x
      = iterValue Y₃ Yt f w₂ w₁ w₃ σ ν (x - 1) 1 := by
  have hx0 : x - 1 ≠ 0 := fun h => by
    rw [show x = 1 by linear_combination h] at hx; simp at hx
  rw [iterValue_one _ _ hx0, iterModel, show x - 1 = -(1 - x) by ring,
    neg_cpow_of_im_neg (by simp only [Complex.sub_im, Complex.one_im]; linarith)]
  ring

/-- On the real segment `t < 1` the modified iterate is the iterate (`e^{πi}` branch, which is
the principal branch of the negative real `t − 1`). -/
theorem iterModel_eq_of_real (σ ν : ℂ) {t : ℝ} (ht : t < 1) :
    iterModel (Y₃ := Y₃) (Yt := Yt) (f := f) (w₁ := w₁) (w₂ := w₂) (w₃ := w₃) σ ν t
      = iterValue Y₃ Yt f w₂ w₁ w₃ σ ν ((t : ℂ) - 1) 1 := by
  have hx0 : (t : ℂ) - 1 ≠ 0 := by
    rw [show (t : ℂ) - 1 = ((t - 1 : ℝ) : ℂ) by push_cast; ring]
    exact_mod_cast (by linarith : t - 1 ≠ 0)
  rw [iterValue_one _ _ hx0, iterModel,
    show (t : ℂ) - 1 = -((1 - t : ℝ) : ℂ) by push_cast; ring,
    neg_cpow_real (by linarith : (0 : ℝ) < 1 - t),
    show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; ring]
  push_cast
  ring

end Model

/-! ## Commutativity as analytic continuation -/

/-- **Half commutativity, analytic form** (TRUE for strongly rational `W`: Huang 2005 CCM 7 §3).
Every product of intertwiners among irreducible modules, continued from `|x| < 1` into the upper
half plane, equals near `x = 1` a finite sum of iterates `⟨f, 𝒴₃ʲ(𝒴̃ʲ(w₂, x−1)w₁, 1)w₃⟩` with the
reversed inner pair and the principal power of `x − 1`; these are holomorphic on the whole upper
half disc `{Im x > 0, |x − 1| < 1}` (`analyticOnNhd_iterValue_upper`). -/
def CommutativityHalf (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (P₁ P₂ P₃ P₄ Q : LWModule W), P₁.IsIrreducibleLW → P₂.IsIrreducibleLW →
    P₃.IsIrreducibleLW → P₄.IsIrreducibleLW → Q.IsIrreducibleLW →
  ∀ (Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier)
    (Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier),
    IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁ →
    IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂ →
  ∃ (r : ℕ) (Qs : Fin r → LWModule W) (_ : ∀ j, (Qs j).IsIrreducibleLW)
    (Y₃ : ∀ j, IntertwiningModes (Qs j).carrier P₃.carrier P₄.carrier)
    (Yt : ∀ j, IntertwiningModes P₂.carrier P₁.carrier (Qs j).carrier),
    (∀ j, IsIntertwiningOperator (Qs j).isMod P₃.isMod P₄.isMod (Y₃ j)) ∧
    (∀ j, IsIntertwiningOperator P₂.isMod P₁.isMod (Qs j).isMod (Yt j)) ∧
    ∀ (α₁ α₂ α₃ h₄ : ℂ) (w₁ : P₁.carrier) (w₂ : P₂.carrier) (w₃ : P₃.carrier)
      (f : P₄.carrier →ₗ[ℂ] ℂ),
      w₁ ∈ P₁.isMod.weight α₁ → w₂ ∈ P₂.isMod.weight α₂ → w₃ ∈ P₃.isMod.weight α₃ →
      SupportedAt P₄.isMod f h₄ →
    ∀ x : ℂ, 0 < x.im → ‖x - 1‖ < 1 / 3 → ‖x‖ < 1 →
      prodValue Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₂ + α₃ - 1 - Q.h) 1 x
        = ∑ j, iterValue (Y₃ j) (Yt j) f w₂ w₁ w₃ (α₁ + α₂ + α₃ - h₄ - 2)
            (α₁ + α₂ - 1 - (Qs j).h) (x - 1) 1

/-- **The real form implies the analytic form** (identity theorem). -/
theorem commutativityHalf_of_halfReal (hV : StronglyRational W) (h : CommutativityHalfReal W) :
    CommutativityHalf W := by
  intro P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂
  obtain ⟨r, Qs, iQs, Y₃, Yt, hY₃, hYt, hreal⟩ := h P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂
  refine ⟨r, Qs, iQs, Y₃, Yt, hY₃, hYt, ?_⟩
  intro α₁ α₂ α₃ h₄ w₁ w₂ w₃ f h₁ h₂ h₃ hf x hxim hx1 hx0
  set σ := α₁ + α₂ + α₃ - h₄ - 2
  set U : Set ℂ := Metric.ball 1 (1 / 3) ∩ Metric.ball 0 1 with hU
  set F := prodModel (Y₁ := Y₁) (Y₂ := Y₂) (f := f) (w₁ := w₁) (w₂ := w₂) (w₃ := w₃) σ
    (α₂ + α₃ - 1 - Q.h) with hF
  set H : ℂ → ℂ := fun z => ∑ j, iterModel (Y₃ := Y₃ j) (Yt := Yt j) (f := f) (w₁ := w₁)
    (w₂ := w₂) (w₃ := w₃) σ (α₁ + α₂ - 1 - (Qs j).h) z with hH
  have hre : ∀ z ∈ U, 2 / 3 < z.re ∧ z.re < 1 := by
    intro z hz
    have h1 := hz.1
    have h2 := hz.2
    rw [Metric.mem_ball, dist_eq_norm] at h1
    rw [Metric.mem_ball, dist_zero_right] at h2
    have a1 := Complex.abs_re_le_norm (z - 1)
    have a2 := Complex.re_le_norm z
    simp only [Complex.sub_re, Complex.one_re] at a1
    constructor
    · have := (abs_lt.1 (lt_of_le_of_lt a1 h1)).1; linarith
    · linarith
  have hFa : AnalyticOnNhd ℂ F U := fun z hz =>
    analyticOnNhd_prodModel hV i₁ i₂ i₃ i₄ hY₁ hY₂ h₁ h₂ h₃ hf z
      ⟨hz.2, by change 0 < z.re; linarith [(hre z hz).1]⟩
  have hHa : AnalyticOnNhd ℂ H U := by
    have := Finset.analyticOnNhd_sum (𝕜 := ℂ) (s := U) Finset.univ
      (f := fun j => iterModel (Y₃ := Y₃ j) (Yt := Yt j) (f := f) (w₁ := w₁) (w₂ := w₂)
        (w₃ := w₃) σ (α₁ + α₂ - 1 - (Qs j).h)) (fun j _ z hz =>
      analyticOnNhd_iterModel hV i₁ i₂ i₃ i₄ (hY₃ j) (hYt j) h₁ h₂ h₃ hf z
        ⟨by
          have h1 := hz.1
          rw [Metric.mem_ball, dist_eq_norm] at h1
          linarith,
         by simp only [Complex.sub_re, Complex.one_re]; linarith [(hre z hz).2]⟩)
    intro z hz
    convert this z hz using 1
    funext y
    simp [hH, Finset.sum_apply]
  have hUc : IsPreconnected U := ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
  -- equality on the real segment
  have hseg : ∀ t : ℝ, 2 / 3 < t → t < 1 → F t = H t := by
    intro t ht1 ht2
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (by linarith : t ≠ 0)
    rw [hF, prodModel, ← prodValue_one _ _ ht0, hreal α₁ α₂ α₃ h₄ w₁ w₂ w₃ f h₁ h₂ h₃ hf t ht1 ht2,
      hH]
    exact Finset.sum_congr rfl fun j _ => (iterModel_eq_of_real _ _ ht2).symm
  -- frequently near `5/6`
  have hfreq : ∃ᶠ z in 𝓝[≠] ((5 / 6 : ℝ) : ℂ), F z = H z := by
    set t : ℕ → ℝ := fun n => 5 / 6 + 1 / ((n : ℝ) + 1) / 12 with ht
    have htpos : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) / 12 := fun n => by positivity
    have htle : ∀ n : ℕ, 1 / ((n : ℝ) + 1) / 12 ≤ 1 / 12 := fun n => by
      have : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      linarith
    have hlim : Tendsto (fun n => ((t n : ℝ) : ℂ)) atTop (𝓝[≠] ((5 / 6 : ℝ) : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h0 : Tendsto t atTop (𝓝 (5 / 6 + 0 / 12)) :=
          (tendsto_one_div_add_atTop_nhds_zero_nat.div_const 12).const_add _
        rw [zero_div, add_zero] at h0
        exact (Complex.continuous_ofReal.tendsto _).comp h0
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, ht]
        intro heq
        have := Complex.ofReal_injective heq
        linarith [htpos n]
    refine hlim.frequently (Frequently.of_forall fun n => ?_)
    exact hseg (t n) (by simp only [ht]; linarith [htpos n]) (by simp only [ht]; linarith [htle n])
  have h56 : ((5 / 6 : ℝ) : ℂ) ∈ U := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, show ((5 / 6 : ℝ) : ℂ) - 1 = ((-1 / 6 : ℝ) : ℂ) by
        push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
      norm_num
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
      norm_num
  have hEq := hFa.eqOn_of_preconnected_of_frequently_eq hHa hUc h56 hfreq
  have hxU : x ∈ U := ⟨by rw [Metric.mem_ball, dist_eq_norm]; exact hx1,
    by rw [Metric.mem_ball, dist_zero_right]; exact hx0⟩
  have hxne : x ≠ 0 := fun h0 => by rw [h0] at hxim; simp at hxim
  rw [prodValue_one _ _ hxne]
  change F x = _
  rw [hEq hxU, hH]
  exact Finset.sum_congr rfl fun j _ => iterModel_eq_of_im_pos _ _ hxim

/-- **Half commutativity, analytic form, from associativity** (strongly rational `W`). -/
theorem commutativityHalf_of_assoc (hV : StronglyRational W) (hA : AssociativityInput W) :
    CommutativityHalf W :=
  commutativityHalf_of_halfReal hV (commutativityHalfReal_of_assoc hV hA)

/-! ## The reversed products near `x = 1` from the right, and full commutativity -/

section Reversed

variable {P₁ P₂ P₃ P₄ R : LWModule W}
  {Y₅ : IntertwiningModes P₂.carrier R.carrier P₄.carrier}
  {Y₆ : IntertwiningModes P₁.carrier P₃.carrier R.carrier}
  {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier} {f : P₄.carrier →ₗ[ℂ] ℂ}

/-- The reversed product at inner point `1`, outer point `x`, as `x^{−a−1}` times a power series
in `x⁻¹`. -/
theorem prodValue_right_one (σ ν : ℂ) {x : ℂ} (hx : x ≠ 0) :
    prodValue Y₅ Y₆ f w₂ w₁ w₃ σ ν x 1
      = x ^ (-(σ - ν) - 1) * ∑' k : ℕ, prodCoeff Y₅ Y₆ f w₂ w₁ w₃ (σ - ν + k) (ν - k)
          * x⁻¹ ^ k := by
  rw [prodValue, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [Complex.one_cpow, mul_one, show -(σ - ν + (k : ℂ)) - 1 = (-(σ - ν) - 1) + (-(k : ℂ)) by
    ring, Complex.cpow_add _ _ hx, Complex.cpow_neg, Complex.cpow_natCast, inv_pow]
  ring

/-- The analytic model of the reversed product. -/
noncomputable def prodModelRight (σ ν : ℂ) (x : ℂ) : ℂ :=
  x ^ (-(σ - ν) - 1) * ∑' k : ℕ, prodCoeff Y₅ Y₆ f w₂ w₁ w₃ (σ - ν + k) (ν - k) * x⁻¹ ^ k

theorem analyticOnNhd_prodModelRight (hV : StronglyRational W) (i₁ : P₁.IsIrreducibleLW)
    (i₂ : P₂.IsIrreducibleLW) (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    (hY₅ : IsIntertwiningOperator P₂.isMod R.isMod P₄.isMod Y₅)
    (hY₆ : IsIntertwiningOperator P₁.isMod P₃.isMod R.isMod Y₆)
    {α₁ α₂ α₃ h₄ : ℂ} (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄) :
    AnalyticOnNhd ℂ (prodModelRight (Y₅ := Y₅) (Y₆ := Y₆) (f := f) (w₁ := w₁) (w₂ := w₂)
        (w₃ := w₃) (α₁ + α₂ + α₃ - h₄ - 2) (α₁ + α₃ - 1 - R.h)) {x | 1 < ‖x‖ ∧ 0 < x.re} := by
  set a := (α₁ + α₂ + α₃ - h₄ - 2) - (α₁ + α₃ - 1 - R.h)
  have hS : AnalyticOnNhd ℂ (fun y => ∑' k : ℕ, prodCoeff Y₅ Y₆ f w₂ w₁ w₃
      ((α₁ + α₂ + α₃ - h₄ - 2) - (α₁ + α₃ - 1 - R.h) + k) ((α₁ + α₃ - 1 - R.h) - k) * y ^ k)
      (Metric.ball 0 1) := by
    refine analyticOnNhd_tsum_pow _ fun r hr0 hr1 => ?_
    have := VOA.Huang.HuangODEContra.summable_prodTerm_of_moduleC2Input
      VOA.Huang.BuhlSpanning.moduleC2Input_holds hV i₂ i₁ i₃ i₄ R.isMod hY₅ hY₆ h₂ h₁ h₃ hf
      (isBase_canonical R hY₆ h₁ h₃) (z₁ := ((1 / r : ℝ) : ℂ)) (z₂ := 1) one_ne_zero
      (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), norm_one,
          one_lt_div hr0]; exact hr1)
    rw [show α₂ + α₁ + α₃ - h₄ - 2 = α₁ + α₂ + α₃ - h₄ - 2 by ring] at this
    refine (this.div_const ((1 / r) ^ (-a.re - 1))).congr fun k => ?_
    have hr' : (0 : ℝ) < 1 / r := by positivity
    rw [Complex.one_cpow, mul_one, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hr', re_aux,
      show -a.re - (k : ℝ) - 1 = (-a.re - 1) + (-(k : ℝ)) by ring, Real.rpow_add hr',
      Real.rpow_neg hr'.le, Real.rpow_natCast, one_div, inv_pow, inv_inv]
    have : 0 < (r⁻¹) ^ (-a.re - 1) := Real.rpow_pos_of_pos (inv_pos.2 hr0) _
    field_simp
  intro x hx
  have hx0 : x ≠ 0 := fun h => by
    have h1 : 1 < ‖x‖ := hx.1
    rw [h, norm_zero] at h1; linarith
  refine (AnalyticAt.cpow analyticAt_id analyticAt_const
    (Complex.mem_slitPlane_iff.2 (Or.inl hx.2))).mul ?_
  have hxi : x⁻¹ ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, norm_inv]
    exact inv_lt_one_of_one_lt₀ hx.1
  exact AnalyticAt.comp (f := fun y : ℂ => y⁻¹) (hS x⁻¹ hxi) (analyticAt_inv hx0)

end Reversed

/-- The iterate `G(x)` is holomorphic wherever `x − 1` lies in the slit plane, `|x − 1| < 1`. -/
theorem analyticOnNhd_iterValue_slit (hV : StronglyRational W) {P₁ P₂ P₃ P₄ R : LWModule W}
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (i₃ : P₃.IsIrreducibleLW)
    (i₄ : P₄.IsIrreducibleLW) {Y₃ : IntertwiningModes R.carrier P₃.carrier P₄.carrier}
    {Yt : IntertwiningModes P₂.carrier P₁.carrier R.carrier}
    (hY₃ : IsIntertwiningOperator R.isMod P₃.isMod P₄.isMod Y₃)
    (hYt : IsIntertwiningOperator P₂.isMod P₁.isMod R.isMod Yt)
    {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
    {f : P₄.carrier →ₗ[ℂ] ℂ} (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄) :
    AnalyticOnNhd ℂ (fun x => iterValue Y₃ Yt f w₂ w₁ w₃ (α₁ + α₂ + α₃ - h₄ - 2)
        (α₁ + α₂ - 1 - R.h) (x - 1) 1) {x | ‖x - 1‖ < 1 ∧ 1 < x.re} := by
  have hS := analyticOnNhd_iterSeries hV i₁ i₂ i₃ i₄ hY₃ hYt h₁ h₂ h₃ hf
  have hopen : IsOpen {x : ℂ | ‖x - 1‖ < 1 ∧ 1 < x.re} :=
    (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_re)
  intro x hx
  have hmodel : AnalyticAt ℂ (fun x : ℂ => (x - 1) ^ (-(α₁ + α₂ - 1 - R.h) - 1)
      * ∑' p : ℕ, iterCoeff Y₃ Yt f w₂ w₁ w₃ ((α₁ + α₂ - 1 - R.h) - p)
        ((α₁ + α₂ + α₃ - h₄ - 2) - (α₁ + α₂ - 1 - R.h) + p) * (x - 1) ^ p) x := by
    refine AnalyticAt.mul ?_ ?_
    · refine AnalyticAt.cpow (analyticAt_id.sub analyticAt_const) analyticAt_const ?_
      refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
      simp only [Complex.sub_re, Complex.one_re]
      linarith [hx.2]
    · have hx1 : x - 1 ∈ Metric.ball (0 : ℂ) 1 := by
        simpa [Metric.mem_ball, dist_zero_right] using hx.1
      exact AnalyticAt.comp (f := fun y : ℂ => y - 1) (hS (x - 1) hx1)
        (analyticAt_id.sub analyticAt_const)
  refine hmodel.congr ?_
  filter_upwards [hopen.mem_nhds hx] with y hy
  have hy0 : y - 1 ≠ 0 := fun h => by
    have := hy.2
    rw [show y = 1 by linear_combination h] at this
    simp at this
  rw [iterValue_one _ _ hy0]

/-- **Commutativity, analytic form** (TRUE for strongly rational `W`: Huang 2005 CCM 7 §3,
Huang 2008 CCM 10).  The product `𝒴₁(w₁,1)𝒴₂(w₂,x)`, continued from `|x| < 1` through the upper
half plane, equals `Σ_j G_j(x)` near `1` (`G_j` the reversed-pair iterates, holomorphic on the
upper half disc), and `Σ_j G_j(x)` equals a finite sum of products in the **opposite order**
`𝒴₅ᵐ(w₂, x)𝒴₆ᵐ(w₁, 1)` on `{|x − 1| < 1/3, Re x > 1}` — in particular on its upper half, where
`|x| > 1`. -/
def CommutativityInput (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (P₁ P₂ P₃ P₄ Q : LWModule W), P₁.IsIrreducibleLW → P₂.IsIrreducibleLW →
    P₃.IsIrreducibleLW → P₄.IsIrreducibleLW → Q.IsIrreducibleLW →
  ∀ (Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier)
    (Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier),
    IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁ →
    IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂ →
  ∃ (r : ℕ) (Qs : Fin r → LWModule W) (_ : ∀ j, (Qs j).IsIrreducibleLW)
    (Y₃ : ∀ j, IntertwiningModes (Qs j).carrier P₃.carrier P₄.carrier)
    (Yt : ∀ j, IntertwiningModes P₂.carrier P₁.carrier (Qs j).carrier)
    (s : ℕ) (Rs : Fin s → LWModule W) (_ : ∀ m, (Rs m).IsIrreducibleLW)
    (Y₅ : ∀ m, IntertwiningModes P₂.carrier (Rs m).carrier P₄.carrier)
    (Y₆ : ∀ m, IntertwiningModes P₁.carrier P₃.carrier (Rs m).carrier),
    (∀ j, IsIntertwiningOperator (Qs j).isMod P₃.isMod P₄.isMod (Y₃ j)) ∧
    (∀ j, IsIntertwiningOperator P₂.isMod P₁.isMod (Qs j).isMod (Yt j)) ∧
    (∀ m, IsIntertwiningOperator P₂.isMod (Rs m).isMod P₄.isMod (Y₅ m)) ∧
    (∀ m, IsIntertwiningOperator P₁.isMod P₃.isMod (Rs m).isMod (Y₆ m)) ∧
    ∀ (α₁ α₂ α₃ h₄ : ℂ) (w₁ : P₁.carrier) (w₂ : P₂.carrier) (w₃ : P₃.carrier)
      (f : P₄.carrier →ₗ[ℂ] ℂ),
      w₁ ∈ P₁.isMod.weight α₁ → w₂ ∈ P₂.isMod.weight α₂ → w₃ ∈ P₃.isMod.weight α₃ →
      SupportedAt P₄.isMod f h₄ →
    (∀ x : ℂ, 0 < x.im → ‖x - 1‖ < 1 / 3 → ‖x‖ < 1 →
      prodValue Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₂ + α₃ - 1 - Q.h) 1 x
        = ∑ j, iterValue (Y₃ j) (Yt j) f w₂ w₁ w₃ (α₁ + α₂ + α₃ - h₄ - 2)
            (α₁ + α₂ - 1 - (Qs j).h) (x - 1) 1) ∧
    (∀ x : ℂ, ‖x - 1‖ < 1 / 3 → 1 < x.re →
      ∑ j, iterValue (Y₃ j) (Yt j) f w₂ w₁ w₃ (α₁ + α₂ + α₃ - h₄ - 2)
            (α₁ + α₂ - 1 - (Qs j).h) (x - 1) 1
        = ∑ m, prodValue (Y₅ m) (Y₆ m) f w₂ w₁ w₃ (α₁ + α₂ + α₃ - h₄ - 2)
            (α₁ + α₃ - 1 - (Rs m).h) x 1)

/-- **The real form implies the analytic form** (identity theorem on both sides of `1`). -/
theorem commutativityInput_of_inputReal (hV : StronglyRational W)
    (h : CommutativityInputReal W) : CommutativityInput W := by
  intro P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂
  obtain ⟨r, Qs, iQs, Y₃, Yt, s, Rs, iRs, Y₅, Y₆, hY₃, hYt, hY₅, hY₆, hc⟩ :=
    h P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂
  refine ⟨r, Qs, iQs, Y₃, Yt, s, Rs, iRs, Y₅, Y₆, hY₃, hYt, hY₅, hY₆, ?_⟩
  intro α₁ α₂ α₃ h₄ w₁ w₂ w₃ f h₁ h₂ h₃ hf
  refine ⟨fun x hxim hx1 hx0 => ?_, fun x hx1 hxre => ?_⟩
  · -- the left half: identity theorem on `ball 1 (1/3) ∩ ball 0 1`
    set σ := α₁ + α₂ + α₃ - h₄ - 2
    set U : Set ℂ := Metric.ball 1 (1 / 3) ∩ Metric.ball 0 1
    set F := prodModel (Y₁ := Y₁) (Y₂ := Y₂) (f := f) (w₁ := w₁) (w₂ := w₂) (w₃ := w₃) σ
      (α₂ + α₃ - 1 - Q.h) with hF
    set H : ℂ → ℂ := fun z => ∑ j, iterModel (Y₃ := Y₃ j) (Yt := Yt j) (f := f) (w₁ := w₁)
      (w₂ := w₂) (w₃ := w₃) σ (α₁ + α₂ - 1 - (Qs j).h) z with hHdef
    have hre : ∀ z ∈ U, 2 / 3 < z.re ∧ z.re < 1 := by
      intro z hz
      have h1 := hz.1
      have h2 := hz.2
      rw [Metric.mem_ball, dist_eq_norm] at h1
      rw [Metric.mem_ball, dist_zero_right] at h2
      have a1 := Complex.abs_re_le_norm (z - 1)
      have a2 := Complex.re_le_norm z
      simp only [Complex.sub_re, Complex.one_re] at a1
      constructor
      · have := (abs_lt.1 (lt_of_le_of_lt a1 h1)).1; linarith
      · linarith
    have hFa : AnalyticOnNhd ℂ F U := fun z hz =>
      analyticOnNhd_prodModel hV i₁ i₂ i₃ i₄ hY₁ hY₂ h₁ h₂ h₃ hf z
        ⟨hz.2, by change 0 < z.re; linarith [(hre z hz).1]⟩
    have hHa : AnalyticOnNhd ℂ H U := by
      have := Finset.analyticOnNhd_sum (𝕜 := ℂ) (s := U) Finset.univ
        (f := fun j => iterModel (Y₃ := Y₃ j) (Yt := Yt j) (f := f) (w₁ := w₁) (w₂ := w₂)
          (w₃ := w₃) σ (α₁ + α₂ - 1 - (Qs j).h)) (fun j _ z hz =>
        analyticOnNhd_iterModel hV i₁ i₂ i₃ i₄ (hY₃ j) (hYt j) h₁ h₂ h₃ hf z
          ⟨by
            have h1 := hz.1
            rw [Metric.mem_ball, dist_eq_norm] at h1
            linarith,
           by simp only [Complex.sub_re, Complex.one_re]; linarith [(hre z hz).2]⟩)
      intro z hz
      convert this z hz using 1
      funext y
      simp [hHdef, Finset.sum_apply]
    have hUc : IsPreconnected U := ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
    have hseg : ∀ t : ℝ, 2 / 3 < t → t < 1 → F t = H t := by
      intro t ht1 ht2
      have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (by linarith : t ≠ 0)
      rw [hF, prodModel, ← prodValue_one _ _ ht0,
        (hc α₁ α₂ α₃ h₄ w₁ w₂ w₃ f h₁ h₂ h₃ hf).1 t ht1 ht2, hHdef]
      exact Finset.sum_congr rfl fun j _ => (iterModel_eq_of_real _ _ ht2).symm
    have hfreq : ∃ᶠ z in 𝓝[≠] ((5 / 6 : ℝ) : ℂ), F z = H z := by
      set t : ℕ → ℝ := fun n => 5 / 6 + 1 / ((n : ℝ) + 1) / 12 with ht
      have htpos : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) / 12 := fun n => by positivity
      have htle : ∀ n : ℕ, 1 / ((n : ℝ) + 1) / 12 ≤ 1 / 12 := fun n => by
        have : 1 / ((n : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
        linarith
      have hlim : Tendsto (fun n => ((t n : ℝ) : ℂ)) atTop (𝓝[≠] ((5 / 6 : ℝ) : ℂ)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, Eventually.of_forall fun n => ?_⟩
        · have h0 : Tendsto t atTop (𝓝 (5 / 6 + 0 / 12)) :=
            (tendsto_one_div_add_atTop_nhds_zero_nat.div_const 12).const_add _
          rw [zero_div, add_zero] at h0
          exact (Complex.continuous_ofReal.tendsto _).comp h0
        · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, ht]
          intro heq
          have := Complex.ofReal_injective heq
          linarith [htpos n]
      refine hlim.frequently (Frequently.of_forall fun n => ?_)
      exact hseg (t n) (by simp only [ht]; linarith [htpos n])
        (by simp only [ht]; linarith [htle n])
    have h56 : ((5 / 6 : ℝ) : ℂ) ∈ U := by
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, show ((5 / 6 : ℝ) : ℂ) - 1 = ((-1 / 6 : ℝ) : ℂ) by
          push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
        norm_num
      · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
        norm_num
    have hEq := hFa.eqOn_of_preconnected_of_frequently_eq hHa hUc h56 hfreq
    have hxU : x ∈ U := ⟨by rw [Metric.mem_ball, dist_eq_norm]; exact hx1,
      by rw [Metric.mem_ball, dist_zero_right]; exact hx0⟩
    have hxne : x ≠ 0 := fun h0 => by rw [h0] at hxim; simp at hxim
    rw [prodValue_one _ _ hxne]
    change F x = _
    rw [hEq hxU, hHdef]
    exact Finset.sum_congr rfl fun j _ => iterModel_eq_of_im_pos _ _ hxim
  · -- the right half: identity theorem on `ball 1 (1/3) ∩ {Re > 1}`
    set σ := α₁ + α₂ + α₃ - h₄ - 2
    set U : Set ℂ := Metric.ball 1 (1 / 3) ∩ {z | 1 < z.re}
    set G : ℂ → ℂ := fun z => ∑ j, iterValue (Y₃ j) (Yt j) f w₂ w₁ w₃ σ
      (α₁ + α₂ - 1 - (Qs j).h) (z - 1) 1 with hG
    set K : ℂ → ℂ := fun z => ∑ m, prodModelRight (Y₅ := Y₅ m) (Y₆ := Y₆ m) (f := f) (w₁ := w₁)
      (w₂ := w₂) (w₃ := w₃) σ (α₁ + α₃ - 1 - (Rs m).h) z with hK
    have hball : ∀ z ∈ U, ‖z - 1‖ < 1 / 3 := fun z hz => by
      have := hz.1; rwa [Metric.mem_ball, dist_eq_norm] at this
    have hGa : AnalyticOnNhd ℂ G U := by
      have := Finset.analyticOnNhd_sum (𝕜 := ℂ) (s := U) Finset.univ
        (f := fun j z => iterValue (Y₃ j) (Yt j) f w₂ w₁ w₃ σ (α₁ + α₂ - 1 - (Qs j).h) (z - 1) 1)
        (fun j _ z hz => analyticOnNhd_iterValue_slit hV i₁ i₂ i₃ i₄ (hY₃ j) (hYt j) h₁ h₂ h₃
          hf z ⟨by linarith [hball z hz], hz.2⟩)
      intro z hz
      convert this z hz using 1
      funext y
      simp [hG, Finset.sum_apply]
    have hKa : AnalyticOnNhd ℂ K U := by
      have := Finset.analyticOnNhd_sum (𝕜 := ℂ) (s := U) Finset.univ
        (f := fun m => prodModelRight (Y₅ := Y₅ m) (Y₆ := Y₆ m) (f := f) (w₁ := w₁) (w₂ := w₂)
          (w₃ := w₃) σ (α₁ + α₃ - 1 - (Rs m).h))
        (fun m _ z hz => analyticOnNhd_prodModelRight hV i₁ i₂ i₃ i₄ (hY₅ m) (hY₆ m) h₁ h₂ h₃
          hf z ⟨lt_of_lt_of_le hz.2 (Complex.re_le_norm z), by
            have : 1 < z.re := hz.2
            linarith⟩)
      intro z hz
      convert this z hz using 1
      funext y
      simp [hK, Finset.sum_apply]
    have hUc : IsPreconnected U :=
      ((convex_ball _ _).inter (convex_halfSpace_re_gt 1)).isPreconnected
    have hseg : ∀ t : ℝ, 1 < t → t < 4 / 3 → G t = K t := by
      intro t ht1 ht2
      have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (by linarith : t ≠ 0)
      have e := (hc α₁ α₂ α₃ h₄ w₁ w₂ w₃ f h₁ h₂ h₃ hf).2 t ht1 (by linarith)
      exact e.trans (Finset.sum_congr rfl fun m _ => prodValue_right_one _ _ ht0)
    have hfreq : ∃ᶠ z in 𝓝[≠] ((7 / 6 : ℝ) : ℂ), G z = K z := by
      set t : ℕ → ℝ := fun n => 7 / 6 + 1 / ((n : ℝ) + 1) / 12 with ht
      have htpos : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) / 12 := fun n => by positivity
      have htle : ∀ n : ℕ, 1 / ((n : ℝ) + 1) / 12 ≤ 1 / 12 := fun n => by
        have : 1 / ((n : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
        linarith
      have hlim : Tendsto (fun n => ((t n : ℝ) : ℂ)) atTop (𝓝[≠] ((7 / 6 : ℝ) : ℂ)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, Eventually.of_forall fun n => ?_⟩
        · have h0 : Tendsto t atTop (𝓝 (7 / 6 + 0 / 12)) :=
            (tendsto_one_div_add_atTop_nhds_zero_nat.div_const 12).const_add _
          rw [zero_div, add_zero] at h0
          exact (Complex.continuous_ofReal.tendsto _).comp h0
        · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, ht]
          intro heq
          have := Complex.ofReal_injective heq
          linarith [htpos n]
      refine hlim.frequently (Frequently.of_forall fun n => ?_)
      exact hseg (t n) (by simp only [ht]; linarith [htpos n])
        (by simp only [ht]; linarith [htle n])
    have h76 : ((7 / 6 : ℝ) : ℂ) ∈ U := by
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, show ((7 / 6 : ℝ) : ℂ) - 1 = ((1 / 6 : ℝ) : ℂ) by
          push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
        norm_num
      · change 1 < ((7 / 6 : ℝ) : ℂ).re
        rw [Complex.ofReal_re]; norm_num
    have hEq := hGa.eqOn_of_preconnected_of_frequently_eq hKa hUc h76 hfreq
    have hxU : x ∈ U := ⟨by rw [Metric.mem_ball, dist_eq_norm]; exact hx1, hxre⟩
    have hxne : x ≠ 0 := fun h0 => by rw [h0] at hxre; simp at hxre; linarith
    change G x = _
    rw [hEq hxU, hK]
    exact Finset.sum_congr rfl fun m _ => (prodValue_right_one _ _ hxne).symm

/-- **Commutativity, analytic form, from associativity and its converse**. -/
theorem commutativityInput_of_assoc (hV : StronglyRational W) (hA : AssociativityInput W)
    (hC : AssociativityConverse W) : CommutativityInput W :=
  commutativityInput_of_inputReal hV (commutativityInputReal_of_assoc hV hA hC)

end VOA.Huang.CommutativityTarget
